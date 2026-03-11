{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
module Strat.Poly.Quote
  ( RefId(..)
  , SharedBindingKind(..)
  , SharedProgram(..)
  , SharedBinding(..)
  , quoteProgram
  , encodeSharedProgram
  , quoteDiagram
  , canonicalizeDiagram
  ) where

import Control.Monad (foldM)
import Data.Text (Text)
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Pipeline
  ( FragmentDecl(..)
  , QuoteTargetLayout(..)
  )
import Strat.Poly.Diagram (Diagram, unionDiagram)
import Strat.Poly.Doctrine (Doctrine(..), lookupGenDeclInDoctrine)
import Strat.Poly.Graph
  ( BinderArg(..)
  , Diagram(..)
  , Edge(..)
  , EdgeId(..)
  , EdgePayload(..)
  , PortId(..)
  , unEdgeId
  , unPortId
  , addEdgePayload
  , canonDiagramRaw
  , emptyDiagram
  , freshPort
  , shiftDiagram
  , validateDiagram
  )
import Strat.Poly.ModeTheory (ModeName)
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Obj (Obj(OVar, OCon), ObjRef(..), ObjName(..), mkCon, pattern OAObj)
import Strat.Poly.Syntax (CodeArg)


newtype RefId = RefId Int
  deriving (Eq, Ord, Show)

data SharedBindingKind
  = SBIncluded
  | SBResidual
  deriving (Eq, Ord, Show)

data SharedProgram = SharedProgram
  { spBaseDoctrine :: Text
  , spMode :: ModeName
  , spInputs :: [RefId]
  , spBindings :: [SharedBinding]
  , spOutputs :: [RefId]
  , spRefTypes :: M.Map RefId Obj
  }
  deriving (Eq, Ord, Show)

data SharedBinding
  = BindGen
      { sbKind :: SharedBindingKind
      , sbEdgeId :: EdgeId
      , sbScope :: [RefId]
      , sbGen :: GenName
      , sbArgs :: [CodeArg]
      , sbIns :: [RefId]
      , sbOuts :: [RefId]
      , sbBinders :: [SharedProgram]
      }
  | BindBox
      { sbEdgeId :: EdgeId
      , sbScope :: [RefId]
      , sbIns :: [RefId]
      , sbOuts :: [RefId]
      , sbInner :: SharedProgram
      }
  | BindFeedback
      { sbEdgeId :: EdgeId
      , sbScope :: [RefId]
      , sbIns :: [RefId]
      , sbOuts :: [RefId]
      , sbBody :: SharedProgram
      }
  deriving (Eq, Ord, Show)

data BindingKey
  = KeyGen GenName [CodeArg] [RefId] [SharedProgram]
  deriving (Eq, Ord, Show)

data QuoteState = QuoteState
  { qsNextRef :: Int
  , qsScope :: [RefId]
  , qsPortRefs :: M.Map PortId RefId
  , qsRefTypes :: M.Map RefId Obj
  , qsBindingsRev :: [SharedBinding]
  , qsMemo :: M.Map BindingKey [RefId]
  }

data NewRefSource
  = NoNewRefs
  | NewRefsDirect [(RefId, PortId)]
  | NewRefsBundled [RefId] PortId

data LocalAccess = LocalAccess
  { laMode :: ModeName
  , laDoctrine :: Doctrine
  , laLayout :: QuoteTargetLayout
  , laRefTypes :: M.Map RefId Obj
  , laBoundary :: [PortId]
  , laCurrentScope :: [RefId]
  , laOldScope :: [RefId]
  , laOldBundlePort :: PortId
  , laNewRefs :: NewRefSource
  }


quoteDiagram
  :: QuoteTargetLayout
  -> Doctrine
  -> Doctrine
  -> ModeName
  -> FragmentDecl
  -> Diagram
  -> Either Text Diagram
quoteDiagram layout baseDoc derivedDoc mode fragment diag = do
  program <- quoteProgram baseDoc mode fragment diag
  encodeSharedProgram layout derivedDoc program


quoteProgram
  :: Doctrine
  -> ModeName
  -> FragmentDecl
  -> Diagram
  -> Either Text SharedProgram
quoteProgram doc mode fragment diag = do
  diag0 <- canonicalizeDiagram diag
  if mode /= dMode diag0
    then Left "quote: mode mismatch"
    else Right ()
  if mode `S.member` dAcyclicModes doc
    then Right ()
    else Left "quote: mode is not declared acyclic"
  let inputs = dIn diag0
  (inputRefs, refTypes0) <- allocBoundaryRefs diag0 inputs
  ordered <- topoOrder diag0
  let initialState =
        QuoteState
          { qsNextRef = length inputRefs
          , qsScope = inputRefs
          , qsPortRefs = M.fromList (zip inputs inputRefs)
          , qsRefTypes = refTypes0
          , qsBindingsRev = []
          , qsMemo = M.empty
          }
  st <- foldM (quoteEdge doc mode fragment diag0) initialState ordered
  outputRefs <- mapM (requirePortRef st) (dOut diag0)
  pure
    SharedProgram
      { spBaseDoctrine = dName doc
      , spMode = mode
      , spInputs = inputRefs
      , spBindings = reverse (qsBindingsRev st)
      , spOutputs = outputRefs
      , spRefTypes = qsRefTypes st
      }


encodeSharedProgram :: QuoteTargetLayout -> Doctrine -> SharedProgram -> Either Text Diagram
encodeSharedProgram layout doc program = do
  ensureTargetLayout doc layout program
  let mode = spMode program
      inputCtx = map (requireRefTy program) (spInputs program)
  let initialBundleTy = refsTy layout mode inputCtx
  let (bundlePort, diag0) = freshPort initialBundleTy (emptyDiagram mode [])
  diag1 <- addEdgePayload (PGen (GenName (qtlInputRefsGen layout)) [] []) [] [bundlePort] diag0
  let access =
        LocalAccess
          { laMode = mode
          , laDoctrine = doc
          , laLayout = layout
          , laRefTypes = spRefTypes program
          , laBoundary = []
          , laCurrentScope = spInputs program
          , laOldScope = spInputs program
          , laOldBundlePort = bundlePort
          , laNewRefs = NoNewRefs
          }
  (progPort, diag2) <- encodeProgramLocal program access diag1 (spBindings program)
  let final = diag2 { dIn = [], dOut = [progPort] }
  validateDiagram final
  pure final


quoteEdge
  :: Doctrine
  -> ModeName
  -> FragmentDecl
  -> Diagram
  -> QuoteState
  -> Edge
  -> Either Text QuoteState
quoteEdge doc mode fragment sourceDiag st edge =
  case ePayload edge of
    PGen gen args bargs -> do
      binders <- mapM (quoteBinderProgram doc mode fragment) bargs
      let included = gen `S.member` frIncludedGens fragment
      if included
        then shareBinding gen args binders
        else emitBinding SBResidual gen args binders
    PBox _ inner -> do
      innerProgram <- quoteNestedProgram doc mode fragment (frCrossBoxes fragment) inner
      inputRefs <- mapPortRefs (eIns edge)
      emitStructuredBinding
        BindBox
          { sbEdgeId = eId edge
          , sbScope = qsScope st
          , sbIns = inputRefs
          , sbOuts = []
          , sbInner = innerProgram
          }
    PFeedback body -> do
      bodyProgram <- quoteNestedProgram doc mode fragment (frCrossFeedback fragment) body
      inputRefs <- mapPortRefs (eIns edge)
      emitStructuredBinding
        BindFeedback
          { sbEdgeId = eId edge
          , sbScope = qsScope st
          , sbIns = inputRefs
          , sbOuts = []
          , sbBody = bodyProgram
          }
    PSplice _ _ -> Left "quote: splice is not allowed in runtime diagrams"
    PTmMeta _ -> Left "quote: term-meta nodes are not allowed in runtime diagrams"
    PInternalDrop -> Left "quote: internal drop nodes are not allowed in runtime diagrams"
  where
    mapPortRefs = mapM (requirePortRef st)

    shareBinding gen args binders = do
      inputRefs <- mapPortRefs (eIns edge)
      let key = KeyGen gen args inputRefs binders
      case M.lookup key (qsMemo st) of
        Just priorOuts ->
          aliasOutputs priorOuts (eOuts edge) st
        Nothing ->
          doEmit SBIncluded gen args binders

    emitBinding kind gen args binders =
      doEmit kind gen args binders

    doEmit kind gen args binders = do
      (outs, st1) <- allocOutputRefs sourceDiag st (eOuts edge)
      let inputRefs = mapPortRefs' (eIns edge)
          binding =
            BindGen
              { sbKind = kind
              , sbEdgeId = eId edge
              , sbScope = qsScope st
              , sbGen = gen
              , sbArgs = args
              , sbIns = inputRefs
              , sbOuts = outs
              , sbBinders = binders
              }
          st2 =
            st1
              { qsBindingsRev = binding : qsBindingsRev st1
              , qsScope = outs <> qsScope st1
              }
      let memo' =
            case kind of
              SBIncluded ->
                M.insert (KeyGen gen args inputRefs binders) outs (qsMemo st2)
              SBResidual ->
                qsMemo st2
      pure st2 { qsMemo = memo' }

    mapPortRefs' ports =
      [ requirePortRefUnsafe st pid
      | pid <- ports
      ]

    emitStructuredBinding mkBinding = do
      (outs, st1) <- allocOutputRefs sourceDiag st (eOuts edge)
      let binding = (mkBinding { sbOuts = outs })
      pure
        st1
          { qsBindingsRev = binding : qsBindingsRev st1
          , qsScope = outs <> qsScope st1
          }


quoteBinderProgram
  :: Doctrine
  -> ModeName
  -> FragmentDecl
  -> BinderArg
  -> Either Text SharedProgram
quoteBinderProgram doc mode fragment barg =
  case barg of
    BAConcrete inner ->
      quoteNestedProgram doc mode fragment (frCrossBinders fragment) inner
    BAMeta _ ->
      Left "quote: binder metavariable is not allowed in runtime diagrams"


quoteNestedProgram
  :: Doctrine
  -> ModeName
  -> FragmentDecl
  -> Bool
  -> Diagram
  -> Either Text SharedProgram
quoteNestedProgram doc mode fragment shouldCross inner =
  quoteProgram doc mode (if shouldCross then fragment else residualFragment fragment) inner


residualFragment :: FragmentDecl -> FragmentDecl
residualFragment fragment =
  fragment
    { frIncludedGens = S.empty
    , frCrossBinders = False
    , frCrossBoxes = False
    , frCrossFeedback = False
    }


allocBoundaryRefs :: Diagram -> [PortId] -> Either Text ([RefId], M.Map RefId Obj)
allocBoundaryRefs diag ports = do
  refs <- mapM allocOne (zip [0 ..] ports)
  pure (map fst refs, M.fromList refs)
  where
    allocOne (i, pid) = do
      ty <- lookupPortTy diag pid
      pure (RefId i, ty)


allocOutputRefs :: Diagram -> QuoteState -> [PortId] -> Either Text ([RefId], QuoteState)
allocOutputRefs diag st ports = do
  pairs <- mapM allocOne (zip [qsNextRef st ..] ports)
  let outs = map fst pairs
      refTypes' = foldr (uncurry M.insert) (qsRefTypes st) pairs
      portRefs' = foldr (\(refId, pid) acc -> M.insert pid refId acc) (qsPortRefs st) (zip outs ports)
  pure
    ( outs
    , st
        { qsNextRef = qsNextRef st + length outs
        , qsRefTypes = refTypes'
        , qsPortRefs = portRefs'
        }
    )
  where
    allocOne (i, pid) = do
      ty <- lookupPortTy diag pid
      pure (RefId i, ty)


aliasOutputs :: [RefId] -> [PortId] -> QuoteState -> Either Text QuoteState
aliasOutputs refs outs st
  | length refs == length outs =
      Right st { qsPortRefs = foldl (\acc (pid, refId) -> M.insert pid refId acc) (qsPortRefs st) (zip outs refs) }
  | otherwise =
      Left "quote: internal output alias arity mismatch"


requirePortRef :: QuoteState -> PortId -> Either Text RefId
requirePortRef st pid =
  case M.lookup pid (qsPortRefs st) of
    Nothing -> Left "quote: missing quoted ref for source port"
    Just refId -> Right refId


requirePortRefUnsafe :: QuoteState -> PortId -> RefId
requirePortRefUnsafe st pid =
  case M.lookup pid (qsPortRefs st) of
    Nothing -> error "quote: internal missing ref id"
    Just refId -> refId


lookupPortTy :: Diagram -> PortId -> Either Text Obj
lookupPortTy diag pid =
  case IM.lookup (unPortId pid) (dPortObj diag) of
    Nothing -> Left "quote: missing source port type"
    Just ty -> Right ty


ensureTargetLayout :: Doctrine -> QuoteTargetLayout -> SharedProgram -> Either Text ()
ensureTargetLayout doc layout program = do
  let mode = spMode program
  let requireGen name =
        case lookupGenDeclInDoctrine ("quote: target doctrine is missing generator " <> name) doc mode (GenName name) of
          Left err -> Left err
          Right _ -> Right ()
  mapM_ requireGen
    [ qtlInputRefsGen layout
    , qtlRefsNilGen layout
    , qtlRefsConsGen layout
    , qtlRefsHeadGen layout
    , qtlRefsTailGen layout
    , qtlDupRefsGen layout
    , qtlDropRefsGen layout
    , qtlReturnRefsGen layout
    , qtlResidualBoxGen layout
    , qtlResidualFeedbackGen layout
    ]
  mapM_ requireBindingGen (spBindings program)
  pure ()
  where
    requireBindingGen binding =
      case binding of
        BindGen { sbKind = kind, sbGen = gen } ->
          case lookupGenDeclInDoctrine ("quote: target doctrine is missing generator " <> bindingGenName layout kind gen) doc (spMode program) (GenName (bindingGenName layout kind gen)) of
            Left err -> Left err
            Right _ -> Right ()
        BindBox {} ->
          Right ()
        BindFeedback {} ->
          Right ()


encodeProgramLocal
  :: SharedProgram
  -> LocalAccess
  -> Diagram
  -> [SharedBinding]
  -> Either Text (PortId, Diagram)
encodeProgramLocal program access diag bindings =
  case bindings of
    [] -> do
      outBundle <- buildSelectedBundleFromCurrent access diag (spOutputs program)
      let progTy = programTy (laLayout access) (laMode access) program
      let (progPort, diag1) = freshPort progTy (snd outBundle)
      diag2 <- addEdgePayload (PGen (GenName (qtlReturnRefsGen (laLayout access))) [] []) [fst outBundle] [progPort] diag1
      pure (progPort, diag2)
    binding:rest ->
      if sbScope binding /= laCurrentScope access
        then Left "quote: internal scope mismatch during encoding"
        else
          case binding of
            BindGen {} ->
              encodeGenBinding program access diag binding rest
            BindBox {} ->
              encodeBoxLikeBinding program access diag binding rest (GenName (qtlResidualBoxGen (laLayout access))) (sbInner binding)
            BindFeedback {} ->
              encodeBoxLikeBinding program access diag binding rest (GenName (qtlResidualFeedbackGen (laLayout access))) (sbBody binding)


encodeGenBinding
  :: SharedProgram
  -> LocalAccess
  -> Diagram
  -> SharedBinding
  -> [SharedBinding]
  -> Either Text (PortId, Diagram)
encodeGenBinding program access diag binding rest = do
  currentBundle <- buildCurrentBundlePort access diag
  let currentScope = laCurrentScope access
      currentCtx = scopeCtx access currentScope
      bundleCopiesNeeded = 1 + length (sbIns binding)
  (bundleCopies, diag1) <- duplicateBundleCopies access currentCtx bundleCopiesNeeded (fst currentBundle) (snd currentBundle)
  (bundleForCtor, inputCopies) <-
    case bundleCopies of
      [] -> Left "quote: internal missing current bundle copies"
      bundleForCtor':restCopies -> Right (bundleForCtor', restCopies)
  (inputPorts, diag2) <- projectRefsWithCopies access currentScope inputCopies diag1 (sbIns binding)
  (binderPorts, diag3) <- embedPrograms access diag2 (sbBinders binding)
  cont <- encodeContinuationDirect program access binding rest
  let progTy = programTy (laLayout access) (laMode access) program
      ctorName = GenName (bindingGenName (laLayout access) (sbKind binding) (sbGen binding))
      ins = bundleForCtor : inputPorts <> binderPorts
      (progPort, diag4) = freshPort progTy diag3
  diag5 <- addEdgePayload (PGen ctorName (sbArgs binding) [BAConcrete cont]) ins [progPort] diag4
  pure (progPort, diag5)


encodeBoxLikeBinding
  :: SharedProgram
  -> LocalAccess
  -> Diagram
  -> SharedBinding
  -> [SharedBinding]
  -> GenName
  -> SharedProgram
  -> Either Text (PortId, Diagram)
encodeBoxLikeBinding program access diag binding rest ctorName innerProgram = do
  currentBundle <- buildCurrentBundlePort access diag
  (bundleForCtor, inputBundlePort, diag1) <-
    if null (sbIns binding)
      then do
        (emptyBundle, diag0) <- buildBundleFromPorts access (snd currentBundle) []
        pure (fst currentBundle, emptyBundle, diag0)
      else do
        let currentCtx = scopeCtx access (laCurrentScope access)
        (copies, diag0) <- duplicateBundleCopies access currentCtx 2 (fst currentBundle) (snd currentBundle)
        case copies of
          [bundleForCtor', bundleForInputs] -> do
            (inputBundlePort', diag2) <- buildSelectedBundleFromBundle access (laCurrentScope access) bundleForInputs diag0 (sbIns binding)
            pure (bundleForCtor', inputBundlePort', diag2)
          _ ->
            Left "quote: internal invalid bundle duplication result"
  innerDiag <- encodeSharedProgram (laLayout access) (laDoctrine access) innerProgram
  (diag2, innerPort) <- embedClosedDiagram diag1 innerDiag
  cont <- encodeContinuationBundled program access binding rest
  let progTy = programTy (laLayout access) (laMode access) program
      ins = [bundleForCtor, inputBundlePort, innerPort]
      (progPort, diag3) = freshPort progTy diag2
  diag4 <- addEdgePayload (PGen ctorName [] [BAConcrete cont]) ins [progPort] diag3
  pure (progPort, diag4)


encodeContinuationDirect :: SharedProgram -> LocalAccess -> SharedBinding -> [SharedBinding] -> Either Text Diagram
encodeContinuationDirect program access binding rest = do
  let mode = laMode access
      layout = laLayout access
      oldScope = sbScope binding
      outs = sbOuts binding
      oldBundleTy = refsTy layout mode (scopeCtx access oldScope)
      outTypes = map (requireRefTy program) outs
      inTypes = [oldBundleTy] <> map (refTy layout mode) outTypes
      (ports, diag0) = allocPortsLocal mode inTypes
      oldBundlePort = head ports
      outPorts = zip outs (tail ports)
      contAccess =
        LocalAccess
          { laMode = mode
          , laDoctrine = laDoctrine access
          , laLayout = layout
          , laRefTypes = spRefTypes program
          , laBoundary = ports
          , laCurrentScope = outs <> oldScope
          , laOldScope = oldScope
          , laOldBundlePort = oldBundlePort
          , laNewRefs = NewRefsDirect outPorts
          }
  (progPort, diag1) <- encodeProgramLocal program contAccess diag0 rest
  let final = diag1 { dIn = ports, dOut = [progPort] }
  validateDiagram final
  pure final


encodeContinuationBundled :: SharedProgram -> LocalAccess -> SharedBinding -> [SharedBinding] -> Either Text Diagram
encodeContinuationBundled program access binding rest = do
  let mode = laMode access
      layout = laLayout access
      oldScope = sbScope binding
      outs = sbOuts binding
      oldBundleTy = refsTy layout mode (scopeCtx access oldScope)
      outBundleTy = refsTy layout mode (map (requireRefTy program) outs)
      inTypes = [oldBundleTy, outBundleTy]
      (ports, diag0) = allocPortsLocal mode inTypes
      oldBundlePort = head ports
      outBundlePort = ports !! 1
      contAccess =
        LocalAccess
          { laMode = mode
          , laDoctrine = laDoctrine access
          , laLayout = layout
          , laRefTypes = spRefTypes program
          , laBoundary = ports
          , laCurrentScope = outs <> oldScope
          , laOldScope = oldScope
          , laOldBundlePort = oldBundlePort
          , laNewRefs = NewRefsBundled outs outBundlePort
          }
  (progPort, diag1) <- encodeProgramLocal program contAccess diag0 rest
  let final = diag1 { dIn = ports, dOut = [progPort] }
  validateDiagram final
  pure final


embedPrograms :: LocalAccess -> Diagram -> [SharedProgram] -> Either Text ([PortId], Diagram)
embedPrograms access host0 programs = foldM step ([], host0) programs
  where
    step (ports, host) program = do
      diag <- encodeSharedProgram (laLayout access) (laDoctrine access) program
      (host', outPort) <- embedClosedDiagram host diag
      pure (ports <> [outPort], host')


embedClosedDiagram :: Diagram -> Diagram -> Either Text (Diagram, PortId)
embedClosedDiagram host sub
  | not (null (dIn sub)) = Left "quote: expected closed subprogram diagram"
  | length (dOut sub) /= 1 = Left "quote: expected single-output subprogram diagram"
  | otherwise = do
      let shifted = shiftDiagram (dNextPort host) (dNextEdge host) sub
      merged <- unionDiagram host shifted
      pure (merged, head (dOut shifted))


buildCurrentBundlePort :: LocalAccess -> Diagram -> Either Text (PortId, Diagram)
buildCurrentBundlePort access diag =
  case laNewRefs access of
    NoNewRefs ->
      pure (laOldBundlePort access, diag)
    NewRefsDirect refs ->
      foldr consOne (Right (laOldBundlePort access, diag)) refs
    NewRefsBundled outs bundlePort ->
      if null outs
        then pure (laOldBundlePort access, diag)
        else do
        (refPorts, diag0) <- projectRefsFromBundle access outs bundlePort diag outs
        foldr consBundled (Right (laOldBundlePort access, diag0)) refPorts
  where
    consBundled refPort acc = do
      (tailPort, diag0) <- acc
      consRefPort access refPort tailPort diag0
    consOne (refId, refPort) acc = do
      (tailPort, diag0) <- acc
      let _ = refId
      consRefPort access refPort tailPort diag0


buildSelectedBundleFromCurrent :: LocalAccess -> Diagram -> [RefId] -> Either Text (PortId, Diagram)
buildSelectedBundleFromCurrent access diag [] = do
  if null (laCurrentScope access)
    then buildBundleFromPorts access diag []
    else do
      (currentBundle, diag0) <- buildCurrentBundlePort access diag
      diag1 <- dropBundlePort access (scopeCtx access (laCurrentScope access)) currentBundle diag0
      buildBundleFromPorts access diag1 []
buildSelectedBundleFromCurrent access diag refs = do
  (currentBundle, diag0) <- buildCurrentBundlePort access diag
  buildSelectedBundleFromBundle access (laCurrentScope access) currentBundle diag0 refs


buildSelectedBundleFromBundle :: LocalAccess -> [RefId] -> PortId -> Diagram -> [RefId] -> Either Text (PortId, Diagram)
buildSelectedBundleFromBundle access scopeIds bundlePort diag [] = do
  diag0 <- dropBundlePort access (scopeCtx access scopeIds) bundlePort diag
  buildBundleFromPorts access diag0 []
buildSelectedBundleFromBundle access scopeIds bundlePort diag refs = do
  (refPorts, diag0) <- projectRefsFromBundle access scopeIds bundlePort diag refs
  buildBundleFromPorts access diag0 refPorts


buildBundleFromPorts :: LocalAccess -> Diagram -> [PortId] -> Either Text (PortId, Diagram)
buildBundleFromPorts access diag refs = do
  let mode = laMode access
      layout = laLayout access
      nilTy = refsTy layout mode []
      (nilPort, diag0) = freshPort nilTy diag
  diag1 <- addEdgePayload (PGen (GenName (qtlRefsNilGen layout)) [] []) [] [nilPort] diag0
  foldr consRef (Right (nilPort, diag1)) refs
  where
    consRef refPort acc = do
      (tailPort, diag0) <- acc
      consRefPort access refPort tailPort diag0


projectRefsFromBundle :: LocalAccess -> [RefId] -> PortId -> Diagram -> [RefId] -> Either Text ([PortId], Diagram)
projectRefsFromBundle access scopeIds bundlePort diag0 refIds = do
  let ctx = scopeCtx access scopeIds
  (copies, diag1) <- duplicateBundleCopies access ctx (length refIds) bundlePort diag0
  projectRefsWithCopies access scopeIds copies diag1 refIds


projectRefsWithCopies :: LocalAccess -> [RefId] -> [PortId] -> Diagram -> [RefId] -> Either Text ([PortId], Diagram)
projectRefsWithCopies access scopeIds bundleCopies diag0 refIds
  | length bundleCopies /= length refIds =
      Left "quote: internal bundle copy arity mismatch"
  | otherwise =
      foldM step ([], diag0) (zip bundleCopies refIds)
  where
    ctx = scopeCtx access scopeIds
    step (ports, diag) (bundleCopy, refId) = do
      (pid, diag1) <- projectRefFromBundle access scopeIds ctx bundleCopy refId diag
      pure (ports <> [pid], diag1)

duplicateBundleCopies :: LocalAccess -> [Obj] -> Int -> PortId -> Diagram -> Either Text ([PortId], Diagram)
duplicateBundleCopies _ _ n _ diag
  | n < 0 =
      Left "quote: internal negative bundle copy request"
duplicateBundleCopies _ _ 0 _ diag = Right ([], diag)
duplicateBundleCopies _ _ 1 bundlePort diag = Right ([bundlePort], diag)
duplicateBundleCopies access ctx n bundlePort diag = do
  let layout = laLayout access
      mode = laMode access
      bundleTy = refsTy layout mode ctx
      (lhsPort, diag1) = freshPort bundleTy diag
      (rhsPort, diag2) = freshPort bundleTy diag1
  diag3 <- addEdgePayload (PGen (GenName (qtlDupRefsGen layout)) [] []) [bundlePort] [lhsPort, rhsPort] diag2
  (rest, diag4) <- duplicateBundleCopies access ctx (n - 1) rhsPort diag3
  pure (lhsPort : rest, diag4)


dropBundlePort :: LocalAccess -> [Obj] -> PortId -> Diagram -> Either Text Diagram
dropBundlePort access ctx bundlePort diag = do
  let layout = laLayout access
      mode = laMode access
      _bundleTy = refsTy layout mode ctx
  addEdgePayload (PGen (GenName (qtlDropRefsGen layout)) [] []) [bundlePort] [] diag


projectRefFromBundle :: LocalAccess -> [RefId] -> [Obj] -> PortId -> RefId -> Diagram -> Either Text (PortId, Diagram)
projectRefFromBundle access scopeIds ctx bundlePort refId diag = do
  idx <-
    case elemIndex refId scopeIds of
      Nothing -> Left "quote: missing ref in current scope"
      Just i -> Right i
  go ctx bundlePort idx diag
  where
    go (ty:rest) port 0 diag0 = do
      let outTy = refTy (laLayout access) (laMode access) ty
          (outPort, diag1) = freshPort outTy diag0
      diag2 <- addEdgePayload (PGen (GenName (qtlRefsHeadGen (laLayout access))) [] []) [port] [outPort] diag1
      pure (outPort, diag2)
    go (_:rest) port n diag0 = do
      let tailTy = refsTy (laLayout access) (laMode access) rest
          (tailPort, diag1) = freshPort tailTy diag0
      diag2 <- addEdgePayload (PGen (GenName (qtlRefsTailGen (laLayout access))) [] []) [port] [tailPort] diag1
      go rest tailPort (n - 1) diag2
    go [] _ _ _ =
      Left "quote: attempted to project past the end of a refs bundle"


consRefPort :: LocalAccess -> PortId -> PortId -> Diagram -> Either Text (PortId, Diagram)
consRefPort access refPort tailPort diag = do
  refTy0 <- lookupPortDiagTy diag refPort
  tailTy <- lookupPortDiagTy diag tailPort
  ctxTail <-
    case tailTy of
      OCon ref [OAObj ctxTy]
        | ref == ObjRef (laMode access) (ObjName (qtlRefsCtor (laLayout access))) ->
            Right (contextFromRefsType (laLayout access) (laMode access) ctxTy)
      _ ->
        Left "quote: expected refs bundle type during refsCons encoding"
  let (outPort, diag1) =
        freshPort
          (refsTy (laLayout access) (laMode access) (refTy0 : ctxTail))
          diag
  diag2 <- addEdgePayload (PGen (GenName (qtlRefsConsGen (laLayout access))) [] []) [refPort, tailPort] [outPort] diag1
  pure (outPort, diag2)


allocPortsLocal :: ModeName -> [Obj] -> ([PortId], Diagram)
allocPortsLocal mode tys = go tys (emptyDiagram mode [])
  where
    go [] diag = ([], diag)
    go (ty:rest) diag =
      let (pid, diag1) = freshPort ty diag
          (pids, diag2) = go rest diag1
       in (pid : pids, diag2)


bindingGenName :: QuoteTargetLayout -> SharedBindingKind -> GenName -> Text
bindingGenName layout kind (GenName g) =
  case kind of
    SBIncluded -> qtlBindingPrefix layout <> g
    SBResidual -> qtlResidualPrefix layout <> g


programTy :: QuoteTargetLayout -> ModeName -> SharedProgram -> Obj
programTy layout mode program =
  progTy layout mode (map (requireRefTy program) (spInputs program)) (map (requireRefTy program) (spOutputs program))


progTy :: QuoteTargetLayout -> ModeName -> [Obj] -> [Obj] -> Obj
progTy layout mode inCtx outCtx =
  mkCon
    (ObjRef mode (ObjName (qtlProgCtor layout)))
    [ OAObj (ctxTy layout mode inCtx)
    , OAObj (ctxTy layout mode outCtx)
    ]


refTy :: QuoteTargetLayout -> ModeName -> Obj -> Obj
refTy layout mode ty =
  mkCon (ObjRef mode (ObjName (qtlRefCtor layout))) [OAObj ty]


refsTy :: QuoteTargetLayout -> ModeName -> [Obj] -> Obj
refsTy layout mode ctx =
  mkCon (ObjRef mode (ObjName (qtlRefsCtor layout))) [OAObj (ctxTy layout mode ctx)]


ctxTy :: QuoteTargetLayout -> ModeName -> [Obj] -> Obj
ctxTy layout mode = foldr step nilTy
  where
    nilTy = mkCon (ObjRef mode (ObjName (qtlCtxNilCtor layout))) []
    step ty acc = mkCon (ObjRef mode (ObjName (qtlCtxConsCtor layout))) [OAObj ty, OAObj acc]


contextFromRefsType :: QuoteTargetLayout -> ModeName -> Obj -> [Obj]
contextFromRefsType layout mode ty =
  case ty of
    OCon ref []
      | ref == ObjRef mode (ObjName (qtlCtxNilCtor layout)) ->
          []
    OCon ref [OAObj headTy, OAObj tailTy]
      | ref == ObjRef mode (ObjName (qtlCtxConsCtor layout)) ->
          headTy : contextFromRefsType layout mode tailTy
    _ ->
      error "quote: expected explicit-sharing context type"


scopeCtx :: LocalAccess -> [RefId] -> [Obj]
scopeCtx access = map refTyFor
  where
    refTyFor refId =
      case M.lookup refId (laRefTypes access) of
        Nothing -> error "quote: internal missing ref type"
        Just ty -> ty


requireRefTy :: SharedProgram -> RefId -> Obj
requireRefTy program refId =
  case M.lookup refId (spRefTypes program) of
    Nothing -> error "quote: internal missing ref type in program"
    Just ty -> ty


lookupPortDiagTy :: Diagram -> PortId -> Either Text Obj
lookupPortDiagTy diag pid =
  case IM.lookup (unPortId pid) (dPortObj diag) of
    Nothing -> Left "quote: missing encoded port type"
    Just ty -> Right ty


topoOrder :: Diagram -> Either Text [Edge]
topoOrder diag =
  if IM.null edgeTable
    then Right []
    else if length orderedIds == IM.size edgeTable
      then mapM lookupEdge orderedIds
      else Left "quote: diagram is cyclic"
  where
    edgeTable = dEdges diag
    edges = IM.elems edgeTable
    edgeIds = map eId edges
    deps0 = M.fromList [(eid, depsFor eid) | eid <- edgeIds]
    dependents = foldl insertDeps M.empty (M.toList deps0)

    insertDeps acc (eid, deps) =
      S.foldl' (\m dep -> M.insertWith S.union dep (S.singleton eid) m) acc deps

    depsFor eid =
      case findEdge eid of
        Nothing -> S.empty
        Just edge ->
          S.fromList
            [ prod
            | p <- eIns edge
            , Just (Just prod) <- [IM.lookup (portInt p) (dProd diag)]
            ]

    ready0 =
      S.fromList
        [ eid
        | (eid, deps) <- M.toList deps0
        , S.null deps
        ]

    orderedIds = go ready0 deps0 []

    go ready deps acc =
      case S.lookupMin ready of
        Nothing -> reverse acc
        Just eid ->
          let readyRest = S.deleteMin ready
              out = M.findWithDefault S.empty eid dependents
              (deps', ready') = S.foldl' (dropDep eid) (deps, readyRest) out
           in go ready' deps' (eid : acc)

    dropDep done (deps, ready) target =
      let old = M.findWithDefault S.empty target deps
          new = S.delete done old
          deps' = M.insert target new deps
          ready' = if S.null new then S.insert target ready else ready
       in (deps', ready')

    findEdge eid =
      IM.lookup (unEdgeId eid) edgeTable

    lookupEdge eid =
      case findEdge eid of
        Nothing -> Left "quote: internal missing edge"
        Just edge -> Right edge

    portInt (PortId i) = i


canonicalizeDiagram :: Diagram -> Either Text Diagram
canonicalizeDiagram = canonDiagramRaw


elemIndex :: Eq a => a -> [a] -> Maybe Int
elemIndex x = go 0
  where
    go _ [] = Nothing
    go i (y:ys)
      | x == y = Just i
      | otherwise = go (i + 1) ys
