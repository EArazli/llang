{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Graph
  ( PortId(..)
  , EdgeId(..)
  , unPortId
  , unEdgeId
  , BinderMetaVar(..)
  , BinderArg(..)
  , EdgePayload(..)
  , Edge(..)
  , Diagram(..)
  , emptyDiagram
  , freshPort
  , addEdge
  , addEdgePayload
  , validateDiagram
  , mergePorts
  , renumberDiagram
  , diagramIsoEq
  , diagramIsoMatchWithVars
  , diagramIsoMatchWithVarsFrom
  , shiftDiagram
  , diagramPortType
  , getPortLabel
  , setPortLabel
  , diagramPortIds
  , unionDisjointIntMap
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.TypeExpr (TypeExpr, TyVar, IxVar, boundIxIndicesType, typeMode)
import Strat.Poly.Names (GenName(..), BoxName(..))
import Strat.Poly.UnifyTy (Subst, emptySubst, unifyTyFlex, applySubstCtx)
import Strat.Poly.Attr (AttrMap, AttrSubst, AttrVar, unifyAttrFlex)
import Strat.Poly.TypePretty (renderType)
import Strat.Poly.TypeTheory (TypeTheory(..))
import Strat.Util.List (dedupe)


newtype PortId = PortId Int deriving (Eq, Ord, Show)
newtype EdgeId = EdgeId Int deriving (Eq, Ord, Show)
newtype BinderMetaVar = BinderMetaVar Text deriving (Eq, Ord, Show)

data BinderArg
  = BAConcrete Diagram
  | BAMeta BinderMetaVar
  deriving (Eq, Ord, Show)

data EdgePayload
  = PGen GenName AttrMap [BinderArg]
  | PBox BoxName Diagram
  | PFeedback Diagram
  | PSplice BinderMetaVar
  deriving (Eq, Ord, Show)

data Edge = Edge
  { eId   :: EdgeId
  , ePayload :: EdgePayload
  , eIns  :: [PortId]
  , eOuts :: [PortId]
  } deriving (Eq, Ord, Show)

data Diagram = Diagram
  { dMode      :: ModeName
  , dIxCtx     :: [TypeExpr]
  , dIn        :: [PortId]
  , dOut       :: [PortId]
  , dPortTy    :: IM.IntMap TypeExpr
  , dPortLabel :: IM.IntMap (Maybe Text)
  , dProd      :: IM.IntMap (Maybe EdgeId)
  , dCons      :: IM.IntMap (Maybe EdgeId)
  , dEdges     :: IM.IntMap Edge
  , dNextPort  :: Int
  , dNextEdge  :: Int
  } deriving (Eq, Ord, Show)

data IsoState extra = IsoState
  { isoPortMap :: M.Map PortId PortId
  , isoEdgeMap :: M.Map EdgeId EdgeId
  , isoUsedPorts :: S.Set PortId
  , isoUsedEdges :: S.Set EdgeId
  , isoQueue :: [(PortId, PortId)]
  , isoExtra :: extra
  } deriving (Eq, Show)

data IsoExtra = IsoExtra
  { ieTySubst :: Subst
  , ieAttrSubst :: AttrSubst
  } deriving (Eq, Show)

data IsoAlgo extra = IsoAlgo
  { iaComparePorts
      :: Diagram
      -> Diagram
      -> extra
      -> TypeExpr
      -> TypeExpr
      -> Either Text [extra]
  , iaComparePayload
      :: (extra -> Diagram -> Diagram -> Either Text [extra])
      -> extra
      -> EdgePayload
      -> EdgePayload
      -> Either Text [extra]
  , iaPayloadShapeOk :: EdgePayload -> EdgePayload -> Bool
  , iaIxCtxOk :: Diagram -> Diagram -> extra -> Bool
  }


emptyDiagram :: ModeName -> [TypeExpr] -> Diagram
emptyDiagram mode ixCtx = Diagram
  { dMode = mode
  , dIxCtx = ixCtx
  , dIn = []
  , dOut = []
  , dPortTy = IM.empty
  , dPortLabel = IM.empty
  , dProd = IM.empty
  , dCons = IM.empty
  , dEdges = IM.empty
  , dNextPort = 0
  , dNextEdge = 0
  }

unPortId :: PortId -> Int
unPortId (PortId k) = k

unEdgeId :: EdgeId -> Int
unEdgeId (EdgeId k) = k

diagramPortIds :: Diagram -> [PortId]
diagramPortIds diag = map PortId (IM.keys (dPortTy diag))

diagramPortType :: Diagram -> PortId -> Maybe TypeExpr
diagramPortType diag pid = IM.lookup (unPortId pid) (dPortTy diag)

getPortLabel :: Diagram -> PortId -> Maybe Text
getPortLabel diag pid =
  case IM.lookup (unPortId pid) (dPortLabel diag) of
    Nothing -> Nothing
    Just label -> label

setPortLabel :: PortId -> Text -> Diagram -> Either Text Diagram
setPortLabel pid name diag =
  if IM.member (unPortId pid) (dPortTy diag)
    then
      Right
        diag
          { dPortLabel = IM.insert (unPortId pid) (Just name) (dPortLabel diag)
          }
    else Left "setPortLabel: port does not exist"

freshPort :: TypeExpr -> Diagram -> (PortId, Diagram)
freshPort ty diag =
  let pid = PortId (dNextPort diag)
      k = unPortId pid
      diag' = diag
        { dPortTy = IM.insert k ty (dPortTy diag)
        , dPortLabel = IM.insert k Nothing (dPortLabel diag)
        , dProd = IM.insert k Nothing (dProd diag)
        , dCons = IM.insert k Nothing (dCons diag)
        , dNextPort = dNextPort diag + 1
        }
  in (pid, diag')

addEdge :: GenName -> [PortId] -> [PortId] -> Diagram -> Either Text Diagram
addEdge gen ins outs diag =
  addEdgePayload (PGen gen M.empty []) ins outs diag

addEdgePayload :: EdgePayload -> [PortId] -> [PortId] -> Diagram -> Either Text Diagram
addEdgePayload payload ins outs diag = do
  case traverse (ensurePortExists diag) (ins <> outs) of
    Left err ->
      Left (err
        <> " (ins=" <> T.pack (show ins)
        <> ", outs=" <> T.pack (show outs)
        <> ", ports=" <> T.pack (show (IM.keys (dPortTy diag)))
        <> ", next=" <> T.pack (show (dNextPort diag))
        <> ")")
    Right _ -> Right ()
  mapM_ (ensureFreeConsumer diag) ins
  mapM_ (ensureFreeProducer diag) outs
  let eid = EdgeId (dNextEdge diag)
  let edge = Edge { eId = eid, ePayload = payload, eIns = ins, eOuts = outs }
  let diag' = diag
        { dEdges = IM.insert (unEdgeId eid) edge (dEdges diag)
        , dCons = foldr (\p -> IM.insert (unPortId p) (Just eid)) (dCons diag) ins
        , dProd = foldr (\p -> IM.insert (unPortId p) (Just eid)) (dProd diag) outs
        , dNextEdge = dNextEdge diag + 1
        }
  pure diag'

ensurePortExists :: Diagram -> PortId -> Either Text ()
ensurePortExists diag pid =
  case IM.lookup (unPortId pid) (dPortTy diag) of
    Nothing ->
      Left ("addEdge: port does not exist: " <> T.pack (show pid))
    Just _ -> Right ()

ensureFreeConsumer :: Diagram -> PortId -> Either Text ()
ensureFreeConsumer diag pid =
  case IM.lookup (unPortId pid) (dCons diag) of
    Just Nothing -> Right ()
    Just (Just _) -> Left "addEdge: port already has consumer"
    Nothing -> Left "addEdge: port missing consumer slot"

ensureFreeProducer :: Diagram -> PortId -> Either Text ()
ensureFreeProducer diag pid =
  case IM.lookup (unPortId pid) (dProd diag) of
    Just Nothing -> Right ()
    Just (Just _) -> Left "addEdge: port already has producer"
    Nothing -> Left "addEdge: port missing producer slot"

validateDiagram :: Diagram -> Either Text ()
validateDiagram diag = do
  ensureKeysets
  ensureBoundaryUnique "inputs" (dIn diag)
  ensureBoundaryUnique "outputs" (dOut diag)
  mapM_ (ensurePortExists diag) (dIn diag)
  mapM_ (ensurePortExists diag) (dOut diag)
  mapM_ (ensureBoundaryEndpoint "input" (dProd diag)) (dIn diag)
  mapM_ (ensureBoundaryEndpoint "output" (dCons diag)) (dOut diag)
  mapM_ checkEdge (IM.elems (dEdges diag))
  mapM_ checkPortMode (IM.toList (dPortTy diag))
  mapM_ checkPort (IM.keys (dPortTy diag))
  pure ()
  where
    ensureKeysets =
      do
        ensureSameKeySet "port types" (dPortTy diag) (dPortLabel diag)
        ensureSameKeySet "port labels" (dPortLabel diag) (dProd diag)
        ensureSameKeySet "port labels" (dPortLabel diag) (dCons diag)
    ensureSameKeySet label left right =
      if IM.keysSet left == IM.keysSet right
        then Right ()
        else Left ("validateDiagram: " <> label <> " keysets mismatch")
    ensureBoundaryUnique label ports =
      let s = S.fromList ports
      in if S.size s == length ports
        then Right ()
        else Left ("validateDiagram: duplicate ports in boundary " <> label)
    ensureBoundaryEndpoint label mp pid =
      case IM.lookup (unPortId pid) mp of
        Just Nothing -> Right ()
        Just (Just _) -> Left ("validateDiagram: boundary " <> label <> " has incident edge")
        Nothing -> Left "validateDiagram: missing incidence entry"
    checkEdge edge = do
      mapM_ (ensurePortExists diag) (eIns edge <> eOuts edge)
      ensureNoDuplicates "ins" (eIns edge)
      ensureNoDuplicates "outs" (eOuts edge)
      ensureNoOverlap (eIns edge) (eOuts edge)
      mapM_ (checkCons edge) (eIns edge)
      mapM_ (checkProd edge) (eOuts edge)
      checkPayload edge
    checkCons edge pid =
      case IM.lookup (unPortId pid) (dCons diag) of
        Just (Just eid) | eid == eId edge -> Right ()
        _ -> Left "validateDiagram: consumer incidence mismatch"
    checkProd edge pid =
      case IM.lookup (unPortId pid) (dProd diag) of
        Just (Just eid) | eid == eId edge -> Right ()
        _ -> Left "validateDiagram: producer incidence mismatch"
    checkPort k = do
      checkEndpoint "producer" (IM.lookup k (dProd diag)) eOuts
      checkEndpoint "consumer" (IM.lookup k (dCons diag)) eIns
      checkBoundaryCompleteness k
      where
        checkEndpoint label entry sel =
          case entry of
            Just Nothing -> Right ()
            Just (Just eid) -> do
              edge <- requireEdge eid
              if PortId k `elem` sel edge
                then Right ()
                else Left ("validateDiagram: " <> label <> " back-pointer mismatch")
            Nothing -> Left "validateDiagram: missing incidence entry"
        checkBoundaryCompleteness k =
          let pid = PortId k
              prodMissing = IM.lookup k (dProd diag) == Just Nothing
              consMissing = IM.lookup k (dCons diag) == Just Nothing
              inBoundary = pid `elem` dIn diag
              outBoundary = pid `elem` dOut diag
          in if prodMissing && not inBoundary
            then Left "validateDiagram: missing boundary input for open port"
            else if consMissing && not outBoundary
              then Left "validateDiagram: missing boundary output for open port"
              else Right ()
    requireEdge eid =
      case IM.lookup (unEdgeId eid) (dEdges diag) of
        Nothing -> Left "validateDiagram: missing edge referenced by incidence"
        Just edge -> Right edge
    requirePortType d pid =
      case diagramPortType d pid of
        Nothing -> Left "validateDiagram: missing port type"
        Just ty -> Right ty
    checkPayload edge =
      case ePayload edge of
        PGen _ _ binderArgs -> mapM_ checkBinderArg binderArgs
        PBox _ inner -> do
          if dMode inner /= dMode diag
            then Left "validateDiagram: box mode mismatch"
            else Right ()
          if dIxCtx inner /= dIxCtx diag
            then Left "validateDiagram: box index context mismatch"
            else Right ()
          validateDiagram inner
          domOuter <- mapM (requirePortType diag) (eIns edge)
          codOuter <- mapM (requirePortType diag) (eOuts edge)
          domInner <- mapM (requirePortType inner) (dIn inner)
          codInner <- mapM (requirePortType inner) (dOut inner)
          if domOuter == domInner && codOuter == codInner
            then Right ()
            else Left "validateDiagram: box boundary mismatch"
        PFeedback inner -> do
          if dMode inner /= dMode diag
            then Left "validateDiagram: feedback mode mismatch"
            else Right ()
          if dIxCtx inner /= dIxCtx diag
            then Left "validateDiagram: feedback index context mismatch"
            else Right ()
          validateDiagram inner
          innerDom <- mapM (requirePortType inner) (dIn inner)
          innerCod <- mapM (requirePortType inner) (dOut inner)
          outerDom <- mapM (requirePortType diag) (eIns edge)
          outerCod <- mapM (requirePortType diag) (eOuts edge)
          if null outerDom
            then Right ()
            else Left "validateDiagram: feedback edge must not consume outer inputs"
          case (innerDom, innerCod) of
            ([stateIn], stateOut : codTail) -> do
              if stateIn /= stateOut
                then Left "validateDiagram: feedback body first output must match input type"
                else Right ()
              if outerCod == codTail
                then Right ()
                else Left "validateDiagram: feedback outer outputs mismatch body outputs"
            _ ->
              Left "validateDiagram: feedback body must have one input and at least one output"
        PSplice _ -> Right ()
    checkBinderArg barg =
      case barg of
        BAConcrete inner -> validateDiagram inner
        BAMeta _ -> Right ()
    ensureNoDuplicates label ports =
      let s = S.fromList ports
      in if S.size s == length ports
        then Right ()
        else Left ("validateDiagram: duplicate ports in edge " <> label)
    ensureNoOverlap ins outs =
      let s = S.fromList ins `S.intersection` S.fromList outs
      in if S.null s
        then Right ()
        else Left "validateDiagram: port appears in both inputs and outputs"
    checkPortMode (k, ty) =
      if typeMode ty == dMode diag
        then
          let bad = S.filter (>= length (dIxCtx diag)) (boundIxIndicesType ty)
           in if S.null bad
                then Right ()
                else Left "validateDiagram: port type uses out-of-scope bound index"
        else
          Left
            ( "validateDiagram: port p" <> T.pack (show k)
                <> " has type in wrong mode (diagram mode "
                <> case dMode diag of ModeName name -> name
                <> ", type "
                <> renderType ty
                <> ")"
            )

mergePorts :: Diagram -> PortId -> PortId -> Either Text Diagram
mergePorts diag keep drop
  | keep == drop = Right diag
  | otherwise = do
      tyKeep <- requireType keep
      tyDrop <- requireType drop
      labelKeep <- requireLabel keep
      labelDrop <- requireLabel drop
      if tyKeep /= tyDrop
        then Left "mergePorts: type mismatch"
        else do
          let prodKeep = IM.lookup (unPortId keep) (dProd diag)
          let prodDrop = IM.lookup (unPortId drop) (dProd diag)
          let consKeep = IM.lookup (unPortId keep) (dCons diag)
          let consDrop = IM.lookup (unPortId drop) (dCons diag)
          prod <- mergeEndpoint "producer" prodKeep prodDrop
          cons <- mergeEndpoint "consumer" consKeep consDrop
          let diag' = diag
                { dPortTy = IM.delete (unPortId drop) (dPortTy diag)
                , dPortLabel =
                    IM.insert
                      (unPortId keep)
                      (mergeLabel labelKeep labelDrop)
                      (IM.delete (unPortId drop) (dPortLabel diag))
                , dProd = IM.insert (unPortId keep) prod (IM.delete (unPortId drop) (dProd diag))
                , dCons = IM.insert (unPortId keep) cons (IM.delete (unPortId drop) (dCons diag))
                , dIn = replacePort keep drop (dIn diag)
                , dOut = replacePort keep drop (dOut diag)
                , dEdges = IM.map (mergeEdge keep drop) (dEdges diag)
                }
          pure diag'
  where
    requireType pid =
      case IM.lookup (unPortId pid) (dPortTy diag) of
        Nothing -> Left "mergePorts: missing port"
        Just ty -> Right ty
    requireLabel pid =
      case IM.lookup (unPortId pid) (dPortLabel diag) of
        Nothing -> Left "mergePorts: missing port"
        Just label -> Right label
    mergeLabel keepLabel dropLabel =
      case keepLabel of
        Nothing -> dropLabel
        Just _ -> keepLabel
    mergeEndpoint label a b =
      case (a, b) of
        (Just (Just e1), Just (Just e2))
          | e1 == e2 -> Right (Just e1)
          | otherwise -> Left ("mergePorts: " <> label <> " conflict")
        (Just (Just e), Just Nothing) -> Right (Just e)
        (Just Nothing, Just (Just e)) -> Right (Just e)
        (Just Nothing, Just Nothing) -> Right Nothing
        _ -> Left "mergePorts: missing incidence entry"
    replacePort keep' drop' =
      dedupe . map (\p -> if p == drop' then keep' else p)
    mergeEdge keep' drop' edge =
      edge { eIns = map replace (eIns edge), eOuts = map replace (eOuts edge) }
      where
        replace p = if p == drop' then keep' else p

shiftDiagram :: Int -> Int -> Diagram -> Diagram
shiftDiagram portOff edgeOff diag =
  let shiftPort (PortId k) = PortId (k + portOff)
      shiftEdge (EdgeId k) = EdgeId (k + edgeOff)
      shiftPorts = map shiftPort
      shiftEdgeRec edge =
        edge
          { eId = shiftEdge (eId edge)
          , ePayload = shiftPayload (ePayload edge)
          , eIns = shiftPorts (eIns edge)
          , eOuts = shiftPorts (eOuts edge)
          }
      shiftPayload payload =
        case payload of
          PGen g attrs bargs -> PGen g attrs (map shiftBinderArg bargs)
          PBox name inner -> PBox name (shiftDiagram portOff edgeOff inner)
          PFeedback inner -> PFeedback (shiftDiagram portOff edgeOff inner)
          PSplice x -> PSplice x
      shiftBinderArg barg =
        case barg of
          BAConcrete inner -> BAConcrete (shiftDiagram portOff edgeOff inner)
          BAMeta x -> BAMeta x
      shiftPortMap = IM.mapKeysMonotonic (+ portOff)
      shiftEdgeMap = IM.mapKeysMonotonic (+ edgeOff)
  in diag
      { dIn = shiftPorts (dIn diag)
      , dOut = shiftPorts (dOut diag)
      , dPortTy = shiftPortMap (dPortTy diag)
      , dPortLabel = shiftPortMap (dPortLabel diag)
      , dProd = shiftPortMap (fmap (fmap shiftEdge) (dProd diag))
      , dCons = shiftPortMap (fmap (fmap shiftEdge) (dCons diag))
      , dEdges = shiftEdgeMap (IM.map shiftEdgeRec (dEdges diag))
      , dNextPort = dNextPort diag + portOff
      , dNextEdge = dNextEdge diag + edgeOff
      }

renumberDiagram :: Diagram -> Either Text Diagram
renumberDiagram diag = do
  let (portMap, nextPort) = assignPorts diag
  let edgeMap = assignEdges diag
  dPortTy' <- buildPortMap portMap (dPortTy diag)
  dPortLabel' <- buildPortMap portMap (dPortLabel diag)
  dProd' <- buildEdgeRefMap portMap edgeMap (dProd diag)
  dCons' <- buildEdgeRefMap portMap edgeMap (dCons diag)
  dEdges' <- buildEdges portMap edgeMap (dEdges diag)
  dIn' <- mapM (requirePort portMap) (dIn diag)
  dOut' <- mapM (requirePort portMap) (dOut diag)
  pure Diagram
    { dMode = dMode diag
    , dIxCtx = dIxCtx diag
    , dIn = dIn'
    , dOut = dOut'
    , dPortTy = dPortTy'
    , dPortLabel = dPortLabel'
    , dProd = dProd'
    , dCons = dCons'
    , dEdges = dEdges'
    , dNextPort = nextPort
    , dNextEdge = M.size edgeMap
    }
  where
    assignPorts d =
      let boundary = dIn d <> dOut d
          (mp0, next0) = foldl assign (M.empty, 0) boundary
          remaining = filter (`M.notMember` mp0) (diagramPortIds d)
          remainingSorted = sortPorts remaining
          (mp1, next1) = foldl assign (mp0, next0) remainingSorted
      in (mp1, next1)
    assign (mp, n) pid =
      if M.member pid mp
        then (mp, n)
        else (M.insert pid (PortId n) mp, n + 1)
    sortPorts = map PortId . IM.keys . IM.fromList . map (\p -> (unPortId p, ()))
    assignEdges d =
      let edges = IM.elems (dEdges d)
          edgesSorted = sortEdges edges
          mp = foldl (\m (i, e) -> M.insert (eId e) (EdgeId i) m) M.empty (zip [0..] edgesSorted)
      in mp
    sortEdges = map snd . M.toAscList . M.fromList . map (\e -> (unEdgeId (eId e), e))
    buildPortMap mp portMap =
      fmap IM.fromList $
        mapM
          (\(k, ty) -> do
            p <- requirePort mp (PortId k)
            pure (unPortId p, ty))
          (IM.toList portMap)
    buildEdgeRefMap mp em refMap =
      fmap IM.fromList $
        mapM
          (\(k, edgeRef) -> do
            p <- requirePort mp (PortId k)
            edgeRef' <- traverse (requireEdge em) edgeRef
            pure (unPortId p, edgeRef'))
          (IM.toList refMap)
    buildEdges mp em edges =
      fmap IM.fromList $
        mapM
          (\edge -> do
            eid <- requireEdge em (eId edge)
            ins <- mapM (requirePort mp) (eIns edge)
            outs <- mapM (requirePort mp) (eOuts edge)
            payload <- mapPayload (ePayload edge)
            pure (unEdgeId eid, edge { eId = eid, ePayload = payload, eIns = ins, eOuts = outs }))
          (IM.elems edges)
    mapPayload payload =
      case payload of
        PGen g attrs bargs -> do
          bargs' <- mapM mapBinderArg bargs
          Right (PGen g attrs bargs')
        PBox name inner -> do
          inner' <- renumberDiagram inner
          Right (PBox name inner')
        PFeedback inner -> do
          inner' <- renumberDiagram inner
          Right (PFeedback inner')
        PSplice x -> Right (PSplice x)
    mapBinderArg barg =
      case barg of
        BAConcrete inner -> BAConcrete <$> renumberDiagram inner
        BAMeta x -> Right (BAMeta x)
    requirePort mp pid =
      case M.lookup pid mp of
        Nothing -> Left "renumberDiagram: missing port mapping"
        Just v -> Right v
    requireEdge mp eid =
      case M.lookup eid mp of
        Nothing -> Left "renumberDiagram: missing edge mapping"
        Just v -> Right v

diagramIsoEq :: Diagram -> Diagram -> Either Text Bool
diagramIsoEq left right =
  fmap (not . null) (diagramIsoWith algoEq () left right)

unionDisjointIntMap :: Text -> IM.IntMap a -> IM.IntMap a -> Either Text (IM.IntMap a)
unionDisjointIntMap label left right =
  let ksL = IM.keysSet left
      ksR = IM.keysSet right
      overlap = IS.toList (IS.intersection ksL ksR)
  in if null overlap
    then Right (IM.union left right)
    else Left (label <> ": key collision " <> T.pack (show overlap))

diagramIsoMatchWithVars
  :: TypeTheory
  -> S.Set TyVar
  -> S.Set IxVar
  -> S.Set AttrVar
  -> Diagram
  -> Diagram
  -> Either Text [(Subst, AttrSubst)]
diagramIsoMatchWithVars tt tyFlex ixFlex attrFlex =
  diagramIsoMatchWithVarsFrom tt tyFlex ixFlex attrFlex emptySubst M.empty

diagramIsoMatchWithVarsFrom
  :: TypeTheory
  -> S.Set TyVar
  -> S.Set IxVar
  -> S.Set AttrVar
  -> Subst
  -> AttrSubst
  -> Diagram
  -> Diagram
  -> Either Text [(Subst, AttrSubst)]
diagramIsoMatchWithVarsFrom tt tyFlex ixFlex attrFlex tySubst attrSubst left right = do
  let initExtra = IsoExtra tySubst attrSubst
  xs <- diagramIsoWith (algoMatch tt tyFlex ixFlex attrFlex) initExtra left right
  pure [ (ieTySubst ex, ieAttrSubst ex) | ex <- xs ]

diagramIsoWith
  :: IsoAlgo extra
  -> extra
  -> Diagram
  -> Diagram
  -> Either Text [extra]
diagramIsoWith algo extra0 left right
  | dMode left /= dMode right = Right []
  | not (iaIxCtxOk algo left right extra0) = Right []
  | length (dIn left) /= length (dIn right) = Right []
  | length (dOut left) /= length (dOut right) = Right []
  | IM.size (dPortTy left) /= IM.size (dPortTy right) = Right []
  | IM.size (dEdges left) /= IM.size (dEdges right) = Right []
  | otherwise =
      case foldl addInit (Just emptyState) initPairs of
        Nothing -> Right []
        Just st0 -> isoSearch st0
  where
    emptyState = IsoState M.empty M.empty S.empty S.empty [] extra0
    initPairs = zip (dIn left) (dIn right) <> zip (dOut left) (dOut right)

    addInit st (p1, p2) = st >>= \st' -> addPortPair st' p1 p2

    recurse extra d1 d2 = diagramIsoWith algo extra d1 d2

    isoSearch st = do
      propagated <- propagateQueue st
      fmap concat (mapM expand propagated)

    expand st
      | done st = Right [isoExtra st]
      | otherwise =
          case pickNextUnmappedEdge st of
            Nothing -> Right []
            Just e1 -> do
              let candidates = filter (edgeCandidate e1) (unmappedEdges st)
              fmap concat
                ( mapM
                    (\e2 -> do
                      sts <- addEdgePair recurse st e1 e2
                      fmap concat (mapM isoSearch sts)
                    )
                    candidates
                )

    done st =
      M.size (isoEdgeMap st) == IM.size (dEdges left)
        && M.size (isoPortMap st) == IM.size (dPortTy left)

    propagateQueue st0 =
      case isoQueue st0 of
        [] -> Right [st0]
        ((p1, p2) : rest) -> do
          ty1 <- requirePortType "diagramIsoWith: missing left port type" left p1
          ty2 <- requirePortType "diagramIsoWith: missing right port type" right p2
          extras <- iaComparePorts algo left right (isoExtra st0) ty1 ty2
          st1s <-
            fmap concat
              ( mapM
                  ( \extra' ->
                      mapIncidentEdges
                        p1
                        p2
                        st0 { isoQueue = rest, isoExtra = extra' }
                  )
                  extras
              )
          fmap concat (mapM propagateQueue st1s)

    mapIncidentEdges p1 p2 st = do
      stProd <-
        mapEndpoint
          (lookupIncidentEdge left (dProd left) p1)
          (lookupIncidentEdge right (dProd right) p2)
          st
      fmap concat
        ( mapM
            ( mapEndpoint
                (lookupIncidentEdge left (dCons left) p1)
                (lookupIncidentEdge right (dCons right) p2)
            )
            stProd
        )

    mapEndpoint Nothing Nothing st = Right [st]
    mapEndpoint (Just e1) (Just e2) st = addEdgePair recurse st e1 e2
    mapEndpoint _ _ _ = Right []

    lookupIncidentEdge diag mp pid =
      case IM.lookup (unPortId pid) mp of
        Just (Just eid) -> IM.lookup (unEdgeId eid) (dEdges diag)
        _ -> Nothing

    addPortPair st p1 p2 =
      case M.lookup p1 (isoPortMap st) of
        Just mapped ->
          if mapped == p2
            then Just st
            else Nothing
        Nothing ->
          if p2 `S.member` isoUsedPorts st
            then Nothing
            else
              Just
                st
                  { isoPortMap = M.insert p1 p2 (isoPortMap st)
                  , isoUsedPorts = S.insert p2 (isoUsedPorts st)
                  , isoQueue = isoQueue st <> [(p1, p2)]
                  }

    addEdgePair recurse' st e1 e2 =
      case M.lookup (eId e1) (isoEdgeMap st) of
        Just mapped ->
          if mapped == eId e2
            then Right [st]
            else Right []
        Nothing ->
          if eId e2 `S.member` isoUsedEdges st
            || length (eIns e1) /= length (eIns e2)
            || length (eOuts e1) /= length (eOuts e2)
            || not (iaPayloadShapeOk algo (ePayload e1) (ePayload e2))
            then Right []
            else do
              extras <- iaComparePayload algo recurse' (isoExtra st) (ePayload e1) (ePayload e2)
              let pairs = zip (eIns e1) (eIns e2) <> zip (eOuts e1) (eOuts e2)
              pure
                [ st''
                | extra' <- extras
                , let st' =
                        st
                          { isoEdgeMap = M.insert (eId e1) (eId e2) (isoEdgeMap st)
                          , isoUsedEdges = S.insert (eId e2) (isoUsedEdges st)
                          , isoExtra = extra'
                          }
                , Just st'' <- [foldl addPair (Just st') pairs]
                ]
      where
        addPair mSt (p1, p2) = mSt >>= \st' -> addPortPair st' p1 p2

    pickNextUnmappedEdge st =
      case filter (\e -> M.notMember (eId e) (isoEdgeMap st)) (IM.elems (dEdges left)) of
        [] -> Nothing
        e : _ -> Just e

    unmappedEdges st =
      [ e
      | e <- IM.elems (dEdges right)
      , eId e `S.notMember` isoUsedEdges st
      ]

    edgeCandidate e1 e2 =
      length (eIns e1) == length (eIns e2)
        && length (eOuts e1) == length (eOuts e2)
        && iaPayloadShapeOk algo (ePayload e1) (ePayload e2)

    requirePortType msg diag pid =
      case diagramPortType diag pid of
        Nothing -> Left msg
        Just ty -> Right ty

algoEq :: IsoAlgo ()
algoEq =
  IsoAlgo
    { iaComparePorts = \_ _ _ ty1 ty2 -> Right [() | ty1 == ty2]
    , iaComparePayload = comparePayload
    , iaPayloadShapeOk = payloadShape
    , iaIxCtxOk = \left right _ -> dIxCtx left == dIxCtx right
    }
  where
    comparePayload recurse _ p1 p2 =
      case (p1, p2) of
        (PGen g1 attrs1 bargs1, PGen g2 attrs2 bargs2)
          | g1 == g2
              && attrs1 == attrs2
              && length bargs1 == length bargs2 ->
              foldl step (Right [()]) (zip bargs1 bargs2)
          | otherwise ->
              Right []
        (PBox _ d1, PBox _ d2) ->
          recurse () d1 d2
        (PFeedback d1, PFeedback d2) ->
          recurse () d1 d2
        (PSplice x, PSplice y)
          | x == y ->
              Right [()]
          | otherwise ->
              Right []
        _ ->
          Right []
      where
        step acc pair = do
          xs <- acc
          fmap concat (mapM (\_ -> compareBinder pair) xs)

        compareBinder (a, b) =
          case (a, b) of
            (BAConcrete d1, BAConcrete d2) ->
              recurse () d1 d2
            (BAMeta x, BAMeta y)
              | x == y ->
                  Right [()]
              | otherwise ->
                  Right []
            _ ->
              Right []

    payloadShape p1 p2 =
      case (p1, p2) of
        (PGen g1 attrs1 bargs1, PGen g2 attrs2 bargs2) ->
          g1 == g2
            && attrs1 == attrs2
            && length bargs1 == length bargs2
            && and (zipWith binderShape bargs1 bargs2)
        (PBox _ _, PBox _ _) -> True
        (PFeedback _, PFeedback _) -> True
        (PSplice x, PSplice y) -> x == y
        _ -> False

    binderShape (BAConcrete _) (BAConcrete _) = True
    binderShape (BAMeta x) (BAMeta y) = x == y
    binderShape _ _ = False

algoMatch
  :: TypeTheory
  -> S.Set TyVar
  -> S.Set IxVar
  -> S.Set AttrVar
  -> IsoAlgo IsoExtra
algoMatch tt tyFlex ixFlex attrFlex =
  IsoAlgo
    { iaComparePorts = comparePorts
    , iaComparePayload = comparePayload
    , iaPayloadShapeOk = payloadShape
    , iaIxCtxOk = ixCtxOk
    }
  where
    ixCtxOk left right extra =
      case
        ( applySubstCtx tt (ieTySubst extra) (dIxCtx left)
        , applySubstCtx tt (ieTySubst extra) (dIxCtx right)
        )
        of
        (Right left', Right right') -> left' == right'
        _ -> False

    comparePorts left _ extra ty1 ty2 =
      case applySubstCtx tt (ieTySubst extra) (dIxCtx left) of
        Left _ -> Right []
        Right ixCtx' ->
          case unifyTyFlex tt ixCtx' tyFlex ixFlex (ieTySubst extra) ty1 ty2 of
            Left _ -> Right []
            Right tySubst' ->
              Right [extra { ieTySubst = tySubst' }]

    comparePayload recurse extra p1 p2 =
      case (p1, p2) of
        (PGen g1 attrs1 bargs1, PGen g2 attrs2 bargs2)
          | g1 /= g2
              || M.keysSet attrs1 /= M.keysSet attrs2
              || length bargs1 /= length bargs2 ->
              Right []
          | otherwise ->
              case foldl unifyField (Right (ieAttrSubst extra)) (M.toList attrs1) of
                Left _ -> Right []
                Right attrSubst ->
                  foldl step (Right [extra { ieAttrSubst = attrSubst }]) (zip bargs1 bargs2)
          where
            unifyField acc (field, term1) = do
              sub <- acc
              case M.lookup field attrs2 of
                Nothing -> Left "diagramIsoMatchWithVars: missing attribute field"
                Just term2 -> unifyAttrFlex attrFlex sub term1 term2

            step acc pair = do
              xs <- acc
              fmap concat (mapM (\ex -> compareBinder ex pair) xs)

            compareBinder ex (a, b) =
              case (a, b) of
                (BAConcrete d1, BAConcrete d2) ->
                  recurse ex d1 d2
                (BAMeta x, BAMeta y)
                  | x == y ->
                      Right [ex]
                  | otherwise ->
                      Right []
                _ ->
                  Right []
        (PBox _ d1, PBox _ d2) ->
          recurse extra d1 d2
        (PFeedback d1, PFeedback d2) ->
          recurse extra d1 d2
        (PSplice x, PSplice y)
          | x == y ->
              Right [extra]
          | otherwise ->
              Right []
        _ ->
          Right []

    payloadShape p1 p2 =
      case (p1, p2) of
        (PGen g1 attrs1 bargs1, PGen g2 attrs2 bargs2) ->
          g1 == g2
            && M.keysSet attrs1 == M.keysSet attrs2
            && length bargs1 == length bargs2
            && and (zipWith binderShape bargs1 bargs2)
        (PBox _ _, PBox _ _) -> True
        (PFeedback _, PFeedback _) -> True
        (PSplice x, PSplice y) -> x == y
        _ -> False

    binderShape (BAConcrete _) (BAConcrete _) = True
    binderShape (BAMeta x) (BAMeta y) = x == y
    binderShape _ _ = False
