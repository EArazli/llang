{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Quote
  ( SharedProgram(..)
  , SharedBinding(..)
  , quoteProgram
  , encodeSharedProgram
  , quoteDiagram
  , canonicalizeDiagram
  ) where

import Control.Monad (foldM)
import Data.Char (isAlphaNum)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Pipeline
  ( FragmentDecl(..)
  , FragmentProduct(..)
  , FragmentRole(..)
  , NamingPolicy(..)
  , QuotePolicy(..)
  )
import Strat.Poly.Attr (AttrMap, AttrLit(..), AttrTerm(..))
import Strat.Poly.Diagram (Diagram, compD, genD, genDWithAttrs, idD, tensorD)
import Strat.Poly.Doctrine (Doctrine(..), doctrineTypeTheory)
import Strat.Poly.Graph
  ( BinderArg(..)
  , Diagram(..)
  , Edge(..)
  , EdgeId(..)
  , EdgePayload(..)
  , PortId(..)
  , addEdgePayload
  , canonDiagramRaw
  , emptyDiagram
  , freshPort
  , getPortLabel
  , validateDiagram
  )
import Strat.Poly.Kernel (ObjName(..))
import Strat.Poly.ModeTheory (ModeName)
import Strat.Poly.Names (BoxName(..), GenName(..))
import Strat.Poly.Obj (mkCon)
import Strat.Poly.TypeTheory (ttCtorTablesByOwner)
import Strat.Poly.Doctrine (lookupCtorRefForOwnerInTables, lookupCtorSigForOwnerInTables)


data SharedProgram = SharedProgram
  { spBaseDoctrine :: Text
  , spMode :: ModeName
  , spInputs :: [PortId]
  , spBindings :: [SharedBinding]
  , spOutputs :: [PortId]
  , spPortNames :: M.Map PortId Text
  }
  deriving (Eq, Ord, Show)


data SharedBinding
  = BindGen
      { sbEdgeId :: EdgeId
      , sbGen :: GenName
      , sbAttrs :: AttrMap
      , sbIns :: [PortId]
      , sbOuts :: [PortId]
      , sbBinders :: [SharedProgram]
      }
  | BindBox
      { sbEdgeId :: EdgeId
      , sbBoxName :: BoxName
      , sbInner :: SharedProgram
      , sbIns :: [PortId]
      , sbOuts :: [PortId]
      }
  | BindFeedback
      { sbEdgeId :: EdgeId
      , sbBody :: SharedProgram
      , sbIns :: [PortId]
      , sbOuts :: [PortId]
      }
  deriving (Eq, Ord, Show)


data BindingKey
  = KeyGen GenName AttrMap [Text] [SharedProgram]
  | KeyBox BoxName [Text] [Text] SharedProgram
  | KeyFeedback [Text] [Text] SharedProgram
  deriving (Eq, Ord, Show)


data QuoteState = QuoteState
  { qsNames :: M.Map PortId Text
  , qsBindingsRev :: [SharedBinding]
  , qsMemo :: M.Map BindingKey [Text]
  }


quoteDiagram
  :: QuotePolicy
  -> Doctrine
  -> Doctrine
  -> ModeName
  -> FragmentDecl
  -> Diagram
  -> Either Text Diagram
quoteDiagram policy baseDoc derivedDoc mode fragment diag = do
  program <- quoteProgram policy baseDoc mode fragment diag
  encodeSharedProgram derivedDoc program


quoteProgram
  :: QuotePolicy
  -> Doctrine
  -> ModeName
  -> FragmentDecl
  -> Diagram
  -> Either Text SharedProgram
quoteProgram policy doc mode fragment diag = do
  diag0 <- canonicalizeDiagram diag
  if mode /= dMode diag0
    then Left "quote: mode mismatch"
    else Right ()
  if mode `S.member` dAcyclicModes doc
    then Right ()
    else Left "quote: mode is not declared acyclic"
  ordered <- topoOrder diag0
  baseNames <- assignPortNames policy diag0
  let boundaryRefs = M.fromList [ (p, refName baseNames p) | p <- dIn diag0 ]
      initialState =
        QuoteState
          { qsNames = boundaryRefs
          , qsBindingsRev = []
          , qsMemo = M.empty
          }
  st <- foldM (quoteEdge doc mode fragment policy baseNames) initialState ordered
  pure
    ( optimizeSharedProgram fragment
        SharedProgram
          { spBaseDoctrine = dName doc
          , spMode = mode
          , spInputs = dIn diag0
          , spBindings = reverse (qsBindingsRev st)
          , spOutputs = dOut diag0
          , spPortNames = qsNames st
          }
    )


encodeSharedProgram :: Doctrine -> SharedProgram -> Either Text Diagram
encodeSharedProgram doc program = do
  tt <- doctrineTypeTheory doc
  let ctorTables = ttCtorTablesByOwner tt
      mode = spMode program
      requireType0 tName = do
        let mRef = lookupCtorRefForOwnerInTables doc ctorTables mode (ObjName tName)
        ref <-
          case mRef of
            Nothing -> Left ("quote: derived doctrine missing constructor " <> tName)
            Just out -> Right out
        sig <- lookupCtorSigForOwnerInTables doc ctorTables mode ref
        if null sig
          then pure (mkCon ref [])
          else Left ("quote: constructor " <> tName <> " must be nullary")
      requireGen gName =
        case M.lookup mode (dGens doc) >>= M.lookup gName of
          Nothing -> Left ("quote: derived doctrine missing generator " <> renderGenNameText gName)
          Just _ -> Right ()
      bindingCtorName (GenName g) = GenName ("let_" <> g)
      portName pid = refName (spPortNames program) pid
  refTy <- requireType0 "Ref"
  refsTy <- requireType0 "RefList"
  letGraphTy <- requireType0 "LetGraph"
  let tensorMany ds =
        case ds of
          [] -> Right (idD mode [])
          d0:rest -> foldM tensorD d0 rest
      genDWithAttrsBinders domCtx codCtx genName attrs bargs = do
        let (inPorts, diag1) = allocPorts domCtx (emptyDiagram mode [])
        let (outPorts, diag2) = allocPorts codCtx diag1
        diag3 <- addEdgePayload (PGen genName attrs bargs) inPorts outPorts diag2
        let diagFinal = diag3 { dIn = inPorts, dOut = outPorts }
        validateDiagram diagFinal
        pure diagFinal
      allocPorts [] diag = ([], diag)
      allocPorts (ty:rest) diag =
        let (pid, diag1) = freshPort ty diag
            (pids, diag2) = allocPorts rest diag1
         in (pid : pids, diag2)
      mkRef name =
        genDWithAttrs mode [] [refTy] (GenName "ref") (M.singleton "name" (ATLit (ALString name)))
      mkRefList names =
        case names of
          [] -> genD mode [] [refsTy] (GenName "refsNil")
          n:rest -> do
            headRef <- mkRef n
            tailRefs <- mkRefList rest
            pair <- tensorD headRef tailRefs
            cons <- genD mode [refTy, refsTy] [refsTy] (GenName "refsCons")
            compD tt cons pair
      applyBindingCtor ctor attrs domCtx binderArgs argDiags = do
        _ <- requireGen ctor
        ctorDiag <- genDWithAttrsBinders domCtx [letGraphTy] ctor attrs binderArgs
        tuple <- tensorMany argDiags
        compD tt ctorDiag tuple
      mkReturnRefs names = do
        refs <- mkRefList names
        ret <- genD mode [refsTy] [letGraphTy] (GenName "returnRefs")
        compD tt ret refs
      mkBinding contDiag binding =
        case binding of
          BindGen _ gen attrs ins outs binders -> do
            let ctor = bindingCtorName gen
            outRefs <- mapM (mkRef . portName) outs
            inRefs <- mapM (mkRef . portName) ins
            binderDiags <- mapM (encodeSharedProgram doc) binders
            let argDiags = outRefs <> inRefs <> binderDiags
                domCtx =
                  replicate (length outs + length ins) refTy
                    <> replicate (length binders) letGraphTy
            applyBindingCtor ctor attrs domCtx [BAConcrete contDiag] argDiags
          BindBox _ box inner ins outs -> do
            outRefs <- mkRefList (map portName outs)
            inRefs <- mkRefList (map portName ins)
            innerDiag <- encodeSharedProgram doc inner
            tuple <- tensorMany [outRefs, inRefs, innerDiag]
            ctor <- genDWithAttrsBinders [refsTy, refsTy, letGraphTy] [letGraphTy] (GenName "letBox") (M.singleton "name" (ATLit (ALString (renderBoxName box)))) [BAConcrete contDiag]
            compD tt ctor tuple
          BindFeedback _ body ins outs -> do
            outRefs <- mkRefList (map portName outs)
            inRefs <- mkRefList (map portName ins)
            bodyProgDiag <- encodeSharedProgram doc body
            tuple <- tensorMany [outRefs, inRefs, bodyProgDiag]
            ctor <- genDWithAttrsBinders [refsTy, refsTy, letGraphTy] [letGraphTy] (GenName "letFeedback") M.empty [BAConcrete contDiag]
            compD tt ctor tuple
  mapM_ requireGen
    [ GenName "ref"
    , GenName "refsNil"
    , GenName "refsCons"
    , GenName "returnRefs"
    , GenName "letBox"
    , GenName "letFeedback"
    , GenName "letGraphProgram"
    ]
  inRefs <- mkRefList (map portName (spInputs program))
  finalBody <- mkReturnRefs (map portName (spOutputs program))
  nestedBody <- foldM mkBinding finalBody (reverse (spBindings program))
  tuple <- tensorD inRefs nestedBody
  build <- genD mode [refsTy, letGraphTy] [letGraphTy] (GenName "letGraphProgram")
  compD tt build tuple
  where
    renderBoxName (BoxName name) = name
    renderGenNameText (GenName name) = name


quoteEdge
  :: Doctrine
  -> ModeName
  -> FragmentDecl
  -> QuotePolicy
  -> M.Map PortId Text
  -> QuoteState
  -> Edge
  -> Either Text QuoteState
quoteEdge doc mode fragment policy baseNames st edge =
  case ePayload edge of
    PGen gen attrs bargs -> do
      binders <- mapM (quoteBinderProgram doc mode fragment policy) bargs
      let role = M.findWithDefault FragResidual gen (frGenRoles fragment)
      case role of
        FragAlias -> aliasOutputs (eIns edge) (eOuts edge) st
        FragDuplicate -> duplicateOutputs (eIns edge) (eOuts edge) st
        FragDiscard -> pure st
        FragShare -> shareBinding gen attrs binders
        FragResidual -> emitBinding gen attrs binders
    PBox name inner -> do
      innerProgram <- quoteNestedProgram doc mode fragment policy (frRecurseBoxes fragment) inner
      let binding =
            BindBox
              { sbEdgeId = eId edge
              , sbBoxName = name
              , sbInner = innerProgram
              , sbIns = eIns edge
              , sbOuts = eOuts edge
              }
      emitFreshBinding binding st
    PFeedback body -> do
      bodyProgram <- quoteNestedProgram doc mode fragment policy (frRecurseFeedback fragment) body
      let binding =
            BindFeedback
              { sbEdgeId = eId edge
              , sbBody = bodyProgram
              , sbIns = eIns edge
              , sbOuts = eOuts edge
              }
      emitFreshBinding binding st
    PSplice _ _ -> Left "quote: splice is not allowed in runtime diagrams"
    PTmMeta _ -> Left "quote: term-meta nodes are not allowed in runtime diagrams"
    PInternalDrop -> Left "quote: internal drop nodes are not allowed in runtime diagrams"
  where
    shareBinding gen attrs binders = do
      inputRefs <- mapM (requirePortRef st) (eIns edge)
      let key = KeyGen gen attrs inputRefs binders
      case M.lookup key (qsMemo st) of
        Just outputRefs ->
          aliasNamedOutputs outputRefs (eOuts edge) st
        Nothing -> do
          let binding =
                BindGen
                  { sbEdgeId = eId edge
                  , sbGen = gen
                  , sbAttrs = attrs
                  , sbIns = eIns edge
                  , sbOuts = eOuts edge
                  , sbBinders = binders
                  }
          st' <- emitFreshBinding binding st
          let outputRefs = map (refName (qsNames st')) (eOuts edge)
          pure st' { qsMemo = M.insert key outputRefs (qsMemo st') }

    emitBinding gen attrs binders =
      emitFreshBinding
        BindGen
          { sbEdgeId = eId edge
          , sbGen = gen
          , sbAttrs = attrs
          , sbIns = eIns edge
          , sbOuts = eOuts edge
          , sbBinders = binders
          }
        st

    aliasOutputs ins outs st0 =
      case ins of
        [inp] -> do
          ref <- requirePortRef st0 inp
          aliasNamedOutputs (replicate (length outs) ref) outs st0
        _ -> Left "quote: alias role expects exactly one input"

    duplicateOutputs ins outs st0 =
      case ins of
        [inp] -> do
          ref <- requirePortRef st0 inp
          aliasNamedOutputs (replicate (length outs) ref) outs st0
        _ -> Left "quote: duplicate role expects exactly one input"

    quoteBinderProgram doc0 mode0 fragment0 policy0 barg =
      case barg of
        BAConcrete inner -> quoteNestedProgram doc0 mode0 fragment0 policy0 (frRecurseBinders fragment0) inner
        BAMeta _ -> Left "quote: binder metavariable is not allowed in runtime diagrams"

    quoteNestedProgram doc0 mode0 fragment0 policy0 recurse inner =
      quoteProgram policy0 doc0 mode0 (if recurse then fragment0 else residualFragment fragment0) inner

    emitFreshBinding binding st0 = do
      let outs = bindingOuts binding
      names <- foldM assignFreshName (qsNames st0) outs
      pure
        st0
          { qsNames = names
          , qsBindingsRev = binding : qsBindingsRev st0
          }

    assignFreshName acc pid =
      if M.member pid acc
        then Right acc
        else Right (M.insert pid (refName baseNames pid) acc)


bindingOuts :: SharedBinding -> [PortId]
bindingOuts binding =
  case binding of
    BindGen { sbOuts = outs } -> outs
    BindBox { sbOuts = outs } -> outs
    BindFeedback { sbOuts = outs } -> outs


aliasNamedOutputs :: [Text] -> [PortId] -> QuoteState -> Either Text QuoteState
aliasNamedOutputs refs outs st
  | length refs == length outs =
      Right st { qsNames = foldl (\acc (pid, ref) -> M.insert pid ref acc) (qsNames st) (zip outs refs) }
  | otherwise =
      Left "quote: alias arity mismatch"


requirePortRef :: QuoteState -> PortId -> Either Text Text
requirePortRef st pid =
  case M.lookup pid (qsNames st) of
    Nothing -> Left "quote: internal missing quoted input ref"
    Just ref -> Right ref


residualFragment :: FragmentDecl -> FragmentDecl
residualFragment fragment =
  fragment { frGenRoles = M.empty }


optimizeSharedProgram :: FragmentDecl -> SharedProgram -> SharedProgram
optimizeSharedProgram fragment =
  prunePortNames
    . eliminateDeadBindings
    . coalesceSharedBindings fragment
    . eliminateProductProjections (frProducts fragment)
    . optimizeNestedPrograms fragment


optimizeNestedPrograms :: FragmentDecl -> SharedProgram -> SharedProgram
optimizeNestedPrograms fragment program =
  program { spBindings = map optimizeBinding (spBindings program) }
  where
    optimizeBinding binding =
      case binding of
        BindGen {} ->
          binding { sbBinders = map (optimizeSharedProgram fragment) (sbBinders binding) }
        BindBox {} ->
          binding { sbInner = optimizeSharedProgram fragment (sbInner binding) }
        BindFeedback {} ->
          binding { sbBody = optimizeSharedProgram fragment (sbBody binding) }


data PairSource = PairSource
  { psProduct :: FragmentProduct
  , psLeftInput :: Text
  , psRightInput :: Text
  }


eliminateProductProjections :: [FragmentProduct] -> SharedProgram -> SharedProgram
eliminateProductProjections products program =
  program
    { spBindings = reverse keptRev
    , spPortNames = names'
    }
  where
    productByCtor = M.fromList [(fpPairCtor productWitness, productWitness) | productWitness <- products]
    leftProjMap = M.fromList [(fpProjLeft productWitness, productWitness) | productWitness <- products]
    rightProjMap = M.fromList [(fpProjRight productWitness, productWitness) | productWitness <- products]
    (keptRev, names', _) = foldl' step ([], spPortNames program, M.empty) (spBindings program)

    step (acc, names, pairs) binding =
      case binding of
        BindGen { sbGen = gen, sbAttrs = attrs, sbIns = [leftIn, rightIn], sbOuts = [pairOut], sbBinders = [] } ->
          case M.lookup gen productByCtor of
            Just productWitness | M.null attrs ->
              let pairRef = refForPort names pairOut
                  leftRef = refForPort names leftIn
                  rightRef = refForPort names rightIn
               in
              ( binding : acc
              , names
              , M.insert pairRef (PairSource productWitness leftRef rightRef) pairs
              )
            _ ->
              (binding : acc, names, pairs)
        BindGen { sbGen = gen, sbAttrs = attrs, sbIns = [pairIn], sbOuts = [projOut], sbBinders = [] } ->
          case M.lookup (refForPort names pairIn) pairs of
            Just pairSource | M.null attrs ->
              case projectionSourceRef gen pairSource of
                Just sourceRef ->
                  let oldRef = refForPort names projOut
                   in
                  ( acc
                  , substituteRef oldRef sourceRef names
                  , substitutePairSourceRef oldRef sourceRef pairs
                  )
                Nothing ->
                  (binding : acc, names, pairs)
            _ ->
              (binding : acc, names, pairs)
        _ ->
          (binding : acc, names, pairs)

    projectionSourceRef gen pairSource
      | Just productWitness <- M.lookup gen leftProjMap
      , productWitness == psProduct pairSource =
          Just (psLeftInput pairSource)
      | Just productWitness <- M.lookup gen rightProjMap
      , productWitness == psProduct pairSource =
          Just (psRightInput pairSource)
      | otherwise =
          Nothing

    substitutePairSourceRef oldRef newRef =
      M.map
        ( \pairSource ->
            pairSource
              { psLeftInput = rewrite (psLeftInput pairSource)
              , psRightInput = rewrite (psRightInput pairSource)
              }
        )
      where
        rewrite ref = if ref == oldRef then newRef else ref


coalesceSharedBindings :: FragmentDecl -> SharedProgram -> SharedProgram
coalesceSharedBindings fragment program =
  program
    { spBindings = reverse keptRev
    , spPortNames = names'
    }
  where
    (keptRev, names', _) = foldl' step ([], spPortNames program, M.empty) (spBindings program)

    step (acc, names, memo) binding =
      case binding of
        BindGen { sbGen = gen, sbAttrs = attrs, sbIns = ins, sbOuts = outs, sbBinders = binders }
          | M.findWithDefault FragResidual gen (frGenRoles fragment) == FragShare
          , not (null outs) ->
              let inputRefs = map (refForPort names) ins
                  outputRefs = map (refForPort names) outs
                  key = KeyGen gen attrs inputRefs binders
               in case M.lookup key memo of
                    Just priorOutputRefs
                      | length priorOutputRefs == length outputRefs ->
                          let rewrites = zip outputRefs priorOutputRefs
                           in
                            ( acc
                            , foldl' (\accNames (oldRef, newRef) -> substituteRef oldRef newRef accNames) names rewrites
                            , foldl' (\accMemo (oldRef, newRef) -> substituteMemoRef oldRef newRef accMemo) memo rewrites
                            )
                    _ ->
                      (binding : acc, names, M.insert key outputRefs memo)
        _ ->
          (binding : acc, names, memo)


substituteMemoRef :: Text -> Text -> M.Map BindingKey [Text] -> M.Map BindingKey [Text]
substituteMemoRef oldRef newRef =
  M.fromListWith preferExisting . map rewriteEntry . M.toList
  where
    preferExisting existing _ = existing
    rewriteEntry (key, outs) = (rewriteKey key, map rewriteRef outs)
    rewriteRef ref = if ref == oldRef then newRef else ref
    rewriteKey key =
      case key of
        KeyGen gen attrs ins binders ->
          KeyGen gen attrs (map rewriteRef ins) binders
        KeyBox box outs ins inner ->
          KeyBox box (map rewriteRef outs) (map rewriteRef ins) inner
        KeyFeedback outs ins inner ->
          KeyFeedback (map rewriteRef outs) (map rewriteRef ins) inner


eliminateDeadBindings :: SharedProgram -> SharedProgram
eliminateDeadBindings program =
  program { spBindings = kept }
  where
    names = spPortNames program
    (_, kept) = foldl' step (S.fromList (map (refForPort names) (spOutputs program)), []) (reverse (spBindings program))

    step (live, acc) binding =
      let outRefs = map (refForPort names) (bindingOuts binding)
       in if null outRefs || any (`S.member` live) outRefs
        then
          ( live `S.union` S.fromList (map (refForPort names) (bindingInputs binding))
          , binding : acc
          )
        else
          (live, acc)


bindingInputs :: SharedBinding -> [PortId]
bindingInputs binding =
  case binding of
    BindGen { sbIns = ins } -> ins
    BindBox { sbIns = ins } -> ins
    BindFeedback { sbIns = ins } -> ins


prunePortNames :: SharedProgram -> SharedProgram
prunePortNames program =
  program { spPortNames = M.restrictKeys (spPortNames program) usedPorts }
  where
    usedPorts =
      S.fromList
        ( spInputs program
            <> spOutputs program
            <> concatMap (\binding -> bindingInputs binding <> bindingOuts binding) (spBindings program)
        )


refForPort :: M.Map PortId Text -> PortId -> Text
refForPort names pid =
  case M.lookup pid names of
    Nothing -> error "quote: internal missing quoted ref name during optimization"
    Just ref -> ref


substituteRef :: Text -> Text -> M.Map PortId Text -> M.Map PortId Text
substituteRef oldRef newRef =
  M.map (\ref -> if ref == oldRef then newRef else ref)


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
      case nextReady ready of
        Nothing -> reverse acc
        Just (eid, readyRest) ->
          let out = M.findWithDefault S.empty eid dependents
              (deps', ready') =
                S.foldl'
                  (dropDep eid)
                  (deps, readyRest)
                  out
           in go ready' deps' (eid : acc)

    dropDep done (deps, ready) target =
      let old = M.findWithDefault S.empty target deps
          new = S.delete done old
          deps' = M.insert target new deps
          ready' = if S.null new then S.insert target ready else ready
       in (deps', ready')

    nextReady ready =
      case S.lookupMin ready of
        Nothing -> Nothing
        Just eid -> Just (eid, S.deleteMin ready)

    findEdge eid =
      let EdgeId k = eid
       in IM.lookup k edgeTable

    lookupEdge eid =
      case findEdge eid of
        Nothing -> Left "quote: internal missing edge"
        Just edge -> Right edge

    portInt (PortId i) = i


assignPortNames :: QuotePolicy -> Diagram -> Either Text (M.Map PortId Text)
assignPortNames pol diag = go S.empty M.empty ordered
  where
    ordered = boundaryItems <> internalItems

    boundaryItems =
      zipWith (\i p -> (p, True, i)) [0 :: Int ..] boundaryOrder

    internalItems =
      zipWith (\i p -> (p, False, i)) [0 :: Int ..] internalOrder

    boundaryOrder = dedupePorts (dIn diag <> dOut diag)
    boundarySet = S.fromList boundaryOrder

    internalOrder =
      [ PortId k
      | k <- IM.keys (dPortObj diag)
      , PortId k `S.notMember` boundarySet
      ]

    go _ acc [] = Right acc
    go used acc ((p, isBoundary, i):ps)
      | M.member p acc = go used acc ps
      | otherwise = do
          base <-
            case qpNaming pol of
              BoundaryLabelsFirst ->
                if isBoundary
                  then
                    case getPortLabel diag p of
                      Just lbl | not (T.null lbl) -> Right (sanitize lbl)
                      _ -> Right ("p" <> T.pack (show i))
                  else
                    Right ("t" <> T.pack (show i))
          name <- uniqueName used base
          go (S.insert name used) (M.insert p name acc) ps

    sanitize txt =
      let mapped = T.map mapChar txt
       in if T.null mapped then "p" else mapped

    mapChar c = if isAlphaNum c || c == '_' then c else '_'

    uniqueName used base =
      if base `S.member` reserved
        then trySuffix 1
        else Right base
      where
        reserved = used `S.union` qpReserved pol

        trySuffix n =
          let candidate = base <> "_" <> T.pack (show n)
           in if candidate `S.member` reserved
                then trySuffix (n + 1)
                else Right candidate

    dedupePorts = goDedupe S.empty []
      where
        goDedupe _ acc [] = reverse acc
        goDedupe seen acc (p:ps)
          | p `S.member` seen = goDedupe seen acc ps
          | otherwise = goDedupe (S.insert p seen) (p : acc) ps


refName :: M.Map PortId Text -> PortId -> Text
refName names pid =
  case M.lookup pid names of
    Just name -> name
    Nothing ->
      case pid of
        PortId i -> "p" <> T.pack (show i)


canonicalizeDiagram :: Diagram -> Either Text Diagram
canonicalizeDiagram = canonDiagramRaw
