{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Quote
  ( RefId(..)
  , SharedBindingKind(..)
  , SharedProgram(..)
  , SharedBinding(..)
  , reflectSharedProgram
  , quoteProgram
  , quoteDiagram
  ) where

import Control.Monad (foldM)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Pipeline (FragmentDecl(..))
import Strat.Poly.DefEq (termExprToDiagramChecked)
import Strat.Poly.Diagram (Diagram, unionDiagram)
import Strat.Poly.Doctrine (Doctrine(..), GenDecl(..), GenParam(..), lookupGenDeclInDoctrine, doctrineTypeTheory)
import Strat.Poly.Graph
  ( BinderArg(..)
  , Diagram(..)
  , Edge(..)
  , EdgePayload(..)
  , PortId(..)
  , addEdgePayload
  , emptyDiagram
  , freshPort
  , shiftDiagram
  , unEdgeId
  , unPortId
  , validateDiagram
  )
import Strat.Poly.ModeTheory (ModeName)
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Literal (Literal(..), LiteralKind(..))
import Strat.Poly.Obj (CodeArg(..), Obj, ObjName(..), ObjRef(..), TermDiagram(..), mkCon, tmvSort)
import Strat.Poly.Term.AST (TermExpr(..), TermHeadArg(..))
import Strat.Poly.TypeTheory (literalKindForObj)


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
      , sbScope :: [RefId]
      , sbGen :: GenName
      , sbArgs :: [CodeArg]
      , sbIns :: [RefId]
      , sbOuts :: [RefId]
      , sbBinders :: [SharedProgram]
      }
  | BindBox
      { sbScope :: [RefId]
      , sbIns :: [RefId]
      , sbOuts :: [RefId]
      , sbInner :: SharedProgram
      }
  | BindFeedback
      { sbScope :: [RefId]
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


quoteDiagram
  :: Doctrine
  -> Doctrine
  -> ModeName
  -> FragmentDecl
  -> Diagram
  -> Either Text Diagram
quoteDiagram baseDoc derivedDoc mode fragment diag = do
  program <- quoteProgram baseDoc mode fragment diag
  reflectSharedProgram derivedDoc program


reflectSharedProgram :: Doctrine -> SharedProgram -> Either Text Diagram
reflectSharedProgram doc program = do
  ensureReflectedTarget doc program
  let mode = spMode program
      seqTy = reflectedSeqTy mode
      progTy = reflectedProgTy mode
  beginArg <- refIdsArg doc mode (spInputs program)
  let (seqPort0, diag0) = freshPort seqTy (emptyDiagram mode [])
  diag1 <- addEdgePayload (PGen reflectedBeginGen [beginArg] []) [] [seqPort0] diag0
  (seqPort1, diag2) <- foldM (reflectBinding doc program) (seqPort0, diag1) (spBindings program)
  endArg <- refIdsArg doc mode (spOutputs program)
  let (progPort, diag3) = freshPort progTy diag2
  diag4 <- addEdgePayload (PGen reflectedEndGen [endArg] []) [seqPort1] [progPort] diag3
  let final = diag4 { dIn = [], dOut = [progPort] }
  validateDiagram final
  pure final


quoteProgram
  :: Doctrine
  -> ModeName
  -> FragmentDecl
  -> Diagram
  -> Either Text SharedProgram
quoteProgram doc mode fragment diag = do
  if mode /= dMode diag
    then Left "quote: mode mismatch"
    else Right ()
  if mode `S.member` dAcyclicModes doc
    then Right ()
    else Left "quote: mode is not declared acyclic"
  validateDiagram diag
  let inputs = dIn diag
  (inputRefs, refTypes0) <- allocBoundaryRefs diag inputs
  ordered <- topoOrder diag
  let initialState =
        QuoteState
          { qsNextRef = length inputRefs
          , qsScope = inputRefs
          , qsPortRefs = M.fromList (zip inputs inputRefs)
          , qsRefTypes = refTypes0
          , qsBindingsRev = []
          , qsMemo = M.empty
          }
  st <- foldM (quoteEdge doc mode fragment diag) initialState ordered
  outputRefs <- mapM (requirePortRef st) (dOut diag)
  pure
    SharedProgram
      { spBaseDoctrine = dName doc
      , spMode = mode
      , spInputs = inputRefs
      , spBindings = reverse (qsBindingsRev st)
      , spOutputs = outputRefs
      , spRefTypes = qsRefTypes st
      }


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
          { sbScope = qsScope st
          , sbIns = inputRefs
          , sbOuts = []
          , sbInner = innerProgram
          }
    PFeedback body -> do
      bodyProgram <- quoteNestedProgram doc mode fragment (frCrossFeedback fragment) body
      inputRefs <- mapPortRefs (eIns edge)
      emitStructuredBinding
        BindFeedback
          { sbScope = qsScope st
          , sbIns = inputRefs
          , sbOuts = []
          , sbBody = bodyProgram
          }
    PSplice _ _ -> Left "quote: splice is not allowed in runtime diagrams"
    PTmMeta _ -> Left "quote: term-meta nodes are not allowed in runtime diagrams"
    PTmLit _ -> Left "quote: literal term nodes are not allowed in runtime diagrams"
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
      let binding = mkBinding { sbOuts = outs }
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


ensureReflectedTarget :: Doctrine -> SharedProgram -> Either Text ()
ensureReflectedTarget doc program = do
  let mode = spMode program
      requireGen name =
        case lookupGenDeclInDoctrine ("quote: target doctrine is missing generator " <> name) doc mode (GenName name) of
          Left err -> Left err
          Right _ -> Right ()
  mapM_ requireGen
    [ "Seq"
    , "Prog"
    , "Digit"
    , "digit0"
    , "digit1"
    , "digit2"
    , "digit3"
    , "digit4"
    , "digit5"
    , "digit6"
    , "digit7"
    , "digit8"
    , "digit9"
    , "RefId"
    , "refId_nil"
    , "refId_cons"
    , "RefIds"
    , "refIds_nil"
    , "refIds_cons"
    , "q_begin"
    , "q_end"
    , "q_res_box"
    , "q_res_feedback"
    ]
  case fastRefIdLabelSort doc mode of
    Left err -> Left err
    Right _ -> Right ()
  mapM_ requireBindingGen (spBindings program)
  pure ()
  where
    requireBindingGen binding =
      case binding of
        BindGen { sbGen = gen } ->
          requireGenText (reflectedBindingGenNameText gen)
        BindBox {} ->
          Right ()
        BindFeedback {} ->
          Right ()
    requireGenText name =
      case lookupGenDeclInDoctrine ("quote: target doctrine is missing generator " <> name) doc (spMode program) (GenName name) of
        Left err -> Left err
        Right _ -> Right ()


reflectBinding :: Doctrine -> SharedProgram -> (PortId, Diagram) -> SharedBinding -> Either Text (PortId, Diagram)
reflectBinding doc program (seqPort, host0) binding =
  case binding of
    BindGen { sbGen = gen, sbArgs = args, sbIns = ins, sbOuts = outs, sbBinders = binders } -> do
      (binderPorts, host1) <- embedPrograms doc host0 binders
      refArgs <- mapM (refIdArg doc (spMode program)) (ins <> outs)
      let seqTy = reflectedSeqTy (spMode program)
          (seqOut, host2) = freshPort seqTy host1
      host3 <-
        addEdgePayload
          (PGen (GenName (reflectedBindingGenNameText gen)) (args <> refArgs) [])
          (seqPort : binderPorts)
          [seqOut]
          host2
      pure (seqOut, host3)
    BindBox { sbIns = ins, sbOuts = outs, sbInner = inner } ->
      reflectStructuredBinding doc program "q_res_box" seqPort host0 ins outs inner
    BindFeedback { sbIns = ins, sbOuts = outs, sbBody = body } ->
      reflectStructuredBinding doc program "q_res_feedback" seqPort host0 ins outs body


reflectStructuredBinding
  :: Doctrine
  -> SharedProgram
  -> Text
  -> PortId
  -> Diagram
  -> [RefId]
  -> [RefId]
  -> SharedProgram
  -> Either Text (PortId, Diagram)
reflectStructuredBinding doc program genName seqPort host0 ins outs nested = do
  (host1, progPort) <- embedProgram doc host0 nested
  inArgs <- refIdsArg doc (spMode program) ins
  outArgs <- refIdsArg doc (spMode program) outs
  let seqTy = reflectedSeqTy (spMode program)
      (seqOut, host2) = freshPort seqTy host1
  host3 <- addEdgePayload (PGen (GenName genName) [inArgs, outArgs] []) [seqPort, progPort] [seqOut] host2
  pure (seqOut, host3)


embedPrograms :: Doctrine -> Diagram -> [SharedProgram] -> Either Text ([PortId], Diagram)
embedPrograms doc host0 programs = foldM step ([], host0) programs
  where
    step (ports, host) program = do
      (host', outPort) <- embedProgram doc host program
      pure (ports <> [outPort], host')


embedProgram :: Doctrine -> Diagram -> SharedProgram -> Either Text (Diagram, PortId)
embedProgram doc host program = do
  diag <- reflectSharedProgram doc program
  embedClosedDiagram host diag


embedClosedDiagram :: Diagram -> Diagram -> Either Text (Diagram, PortId)
embedClosedDiagram host sub
  | not (null (dIn sub)) = Left "quote: expected closed subprogram diagram"
  | length (dOut sub) /= 1 = Left "quote: expected single-output subprogram diagram"
  | otherwise = do
      let shifted = shiftDiagram (dNextPort host) (dNextEdge host) sub
      merged <- unionDiagram host shifted
      case dOut shifted of
        [outPort] -> pure (merged, outPort)
        _ -> Left "quote: expected single embedded output"


refIdArg :: Doctrine -> ModeName -> RefId -> Either Text CodeArg
refIdArg doc mode refId = CATm <$> refIdTerm doc mode refId


refIdTerm :: Doctrine -> ModeName -> RefId -> Either Text TermDiagram
refIdTerm doc mode refId = do
  tt <- doctrineTypeTheory doc
  refExpr <-
    case fastRefIdLabelSort doc mode of
      Left err -> Left err
      Right (Just _) -> Right (refIdLabelExpr refId)
      Right Nothing -> Right (refIdExpr refId)
  termExprToDiagramChecked tt [] (reflectedRefIdTy mode) refExpr


refIdsArg :: Doctrine -> ModeName -> [RefId] -> Either Text CodeArg
refIdsArg doc mode refIds = CATm <$> refIdsTerm doc mode refIds


refIdsTerm :: Doctrine -> ModeName -> [RefId] -> Either Text TermDiagram
refIdsTerm doc mode refIds = do
  tt <- doctrineTypeTheory doc
  refExpr <-
    case fastRefIdLabelSort doc mode of
      Left err -> Left err
      Right (Just _) -> Right (refIdsExpr refIdLabelExpr refIds)
      Right Nothing -> Right (refIdsExpr refIdExpr refIds)
  termExprToDiagramChecked tt [] (reflectedRefIdsTy mode) refExpr


refIdExpr :: RefId -> TermExpr
refIdExpr (RefId n) =
  foldr consTail refIdNilExpr (map digitExpr (refIdDigits n))
  where
    consTail digit tailExpr =
      TMGen reflectedRefIdConsGen [THATm digit, THATm tailExpr]


refIdLabelExpr :: RefId -> TermExpr
refIdLabelExpr refId =
  TMGen reflectedRefIdLabelGen [THATm (TMLit (LString (refIdLabelText refId)))]


refIdsExpr :: (RefId -> TermExpr) -> [RefId] -> TermExpr
refIdsExpr refExpr =
  foldr consTail refIdsNilExpr
  where
    consTail refId tailExpr =
      TMGen reflectedRefIdsConsGen [THATm (refExpr refId), THATm tailExpr]


digitExpr :: Int -> TermExpr
digitExpr n = TMGen (reflectedDigitGen n) []


refIdDigits :: Int -> [Int]
refIdDigits n
  | n < 0 = error "quote: internal negative ref id"
  | n == 0 = [0]
  | otherwise = reverse (go n)
  where
    go k
      | k <= 0 = []
      | otherwise =
          let (q, r) = quotRem k 10
           in r : go q


reflectedDigitGen :: Int -> GenName
reflectedDigitGen n =
  case n of
    0 -> GenName "digit0"
    1 -> GenName "digit1"
    2 -> GenName "digit2"
    3 -> GenName "digit3"
    4 -> GenName "digit4"
    5 -> GenName "digit5"
    6 -> GenName "digit6"
    7 -> GenName "digit7"
    8 -> GenName "digit8"
    9 -> GenName "digit9"
    _ -> error "quote: internal digit out of range"


refIdNilExpr :: TermExpr
refIdNilExpr = TMGen reflectedRefIdNilGen []


refIdsNilExpr :: TermExpr
refIdsNilExpr = TMGen reflectedRefIdsNilGen []


reflectedBindingGenNameText :: GenName -> Text
reflectedBindingGenNameText (GenName name) = "q_" <> name


reflectedSeqTy :: ModeName -> Obj
reflectedSeqTy mode = mkCon (ObjRef mode (ObjName "Seq")) []


reflectedProgTy :: ModeName -> Obj
reflectedProgTy mode = mkCon (ObjRef mode (ObjName "Prog")) []


reflectedRefIdTy :: ModeName -> Obj
reflectedRefIdTy mode = mkCon (ObjRef mode (ObjName "RefId")) []


reflectedRefIdsTy :: ModeName -> Obj
reflectedRefIdsTy mode = mkCon (ObjRef mode (ObjName "RefIds")) []


reflectedRefIdNilGen :: GenName
reflectedRefIdNilGen = GenName "refId_nil"


reflectedRefIdConsGen :: GenName
reflectedRefIdConsGen = GenName "refId_cons"


reflectedRefIdLabelGen :: GenName
reflectedRefIdLabelGen = GenName "refId_label"


reflectedRefIdsNilGen :: GenName
reflectedRefIdsNilGen = GenName "refIds_nil"


reflectedRefIdsConsGen :: GenName
reflectedRefIdsConsGen = GenName "refIds_cons"


fastRefIdLabelSort :: Doctrine -> ModeName -> Either Text (Maybe Obj)
fastRefIdLabelSort doc mode = do
  tt <- doctrineTypeTheory doc
  case lookupGenDeclInDoctrine "" doc mode reflectedRefIdLabelGen of
    Left _ -> Right Nothing
    Right gd ->
      case gdParams gd of
        [GP_Tm tmv]
          | null (gdDom gd)
              && gdCod gd == [reflectedRefIdTy mode]
              && literalKindForObj tt (tmvSort tmv) == Just LKString ->
              Right (Just (tmvSort tmv))
          | otherwise ->
              Left "quote: reflected refId_label must be [] -> [RefId] with a single string-literal term parameter"
        _ ->
          Left "quote: reflected refId_label must be [] -> [RefId] with a single string-literal term parameter"


refIdLabelText :: RefId -> Text
refIdLabelText (RefId n) = T.pack (show n)


reflectedBeginGen :: GenName
reflectedBeginGen = GenName "q_begin"


reflectedEndGen :: GenName
reflectedEndGen = GenName "q_end"


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
