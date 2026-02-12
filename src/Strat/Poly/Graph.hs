{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Graph
  ( PortId(..)
  , EdgeId(..)
  , BinderMetaVar(..)
  , BinderArg(..)
  , FeedbackSpec(..)
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
import Strat.Poly.UnifyTy (Subst, emptySubst, unifyTyFlex, applySubstTy, composeSubst)
import Strat.Poly.Attr (AttrMap, AttrSubst, AttrVar, applyAttrSubstMap, composeAttrSubst, unifyAttrFlex)
import Strat.Poly.TypePretty (renderType)
import Strat.Poly.TypeTheory (TypeTheory(..))


newtype PortId = PortId Int deriving (Eq, Ord, Show)
newtype EdgeId = EdgeId Int deriving (Eq, Ord, Show)
newtype BinderMetaVar = BinderMetaVar Text deriving (Eq, Ord, Show)

data BinderArg
  = BAConcrete Diagram
  | BAMeta BinderMetaVar
  deriving (Eq, Ord, Show)

data FeedbackSpec = FeedbackSpec
  { fbTy :: TypeExpr
  , fbOutArity :: Int
  } deriving (Eq, Ord, Show)

data EdgePayload
  = PGen GenName AttrMap [BinderArg]
  | PBox BoxName Diagram
  | PFeedback FeedbackSpec Diagram
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

data IsoState = IsoState
  { isPortMap :: M.Map PortId PortId
  , isEdgeMap :: M.Map EdgeId EdgeId
  , isUsedPorts :: S.Set PortId
  , isUsedEdges :: S.Set EdgeId
  , isQueue :: [(PortId, PortId)]
  } deriving (Eq, Show)

data IsoMatchState = IsoMatchState
  { imsPortMap :: M.Map PortId PortId
  , imsEdgeMap :: M.Map EdgeId EdgeId
  , imsUsedPorts :: S.Set PortId
  , imsUsedEdges :: S.Set EdgeId
  , imsQueue :: [(PortId, PortId)]
  , imsTySubst :: Subst
  , imsAttrSubst :: AttrSubst
  } deriving (Eq, Show)


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

portKey :: PortId -> Int
portKey (PortId k) = k

edgeKey :: EdgeId -> Int
edgeKey (EdgeId k) = k

diagramPortIds :: Diagram -> [PortId]
diagramPortIds diag = map PortId (IM.keys (dPortTy diag))

diagramPortType :: Diagram -> PortId -> Maybe TypeExpr
diagramPortType diag pid = IM.lookup (portKey pid) (dPortTy diag)

getPortLabel :: Diagram -> PortId -> Maybe Text
getPortLabel diag pid =
  case IM.lookup (portKey pid) (dPortLabel diag) of
    Nothing -> Nothing
    Just label -> label

setPortLabel :: PortId -> Text -> Diagram -> Either Text Diagram
setPortLabel pid name diag =
  if IM.member (portKey pid) (dPortTy diag)
    then
      Right
        diag
          { dPortLabel = IM.insert (portKey pid) (Just name) (dPortLabel diag)
          }
    else Left "setPortLabel: port does not exist"

freshPort :: TypeExpr -> Diagram -> (PortId, Diagram)
freshPort ty diag =
  let pid = PortId (dNextPort diag)
      k = portKey pid
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
        { dEdges = IM.insert (edgeKey eid) edge (dEdges diag)
        , dCons = foldr (\p -> IM.insert (portKey p) (Just eid)) (dCons diag) ins
        , dProd = foldr (\p -> IM.insert (portKey p) (Just eid)) (dProd diag) outs
        , dNextEdge = dNextEdge diag + 1
        }
  pure diag'

ensurePortExists :: Diagram -> PortId -> Either Text ()
ensurePortExists diag pid =
  case IM.lookup (portKey pid) (dPortTy diag) of
    Nothing ->
      Left ("addEdge: port does not exist: " <> T.pack (show pid))
    Just _ -> Right ()

ensureFreeConsumer :: Diagram -> PortId -> Either Text ()
ensureFreeConsumer diag pid =
  case IM.lookup (portKey pid) (dCons diag) of
    Just Nothing -> Right ()
    Just (Just _) -> Left "addEdge: port already has consumer"
    Nothing -> Left "addEdge: port missing consumer slot"

ensureFreeProducer :: Diagram -> PortId -> Either Text ()
ensureFreeProducer diag pid =
  case IM.lookup (portKey pid) (dProd diag) of
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
      case IM.lookup (portKey pid) mp of
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
      case IM.lookup (portKey pid) (dCons diag) of
        Just (Just eid) | eid == eId edge -> Right ()
        _ -> Left "validateDiagram: consumer incidence mismatch"
    checkProd edge pid =
      case IM.lookup (portKey pid) (dProd diag) of
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
      case IM.lookup (edgeKey eid) (dEdges diag) of
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
        PFeedback spec inner -> do
          if dMode inner /= dMode diag
            then Left "validateDiagram: feedback mode mismatch"
            else Right ()
          if dIxCtx inner /= dIxCtx diag
            then Left "validateDiagram: feedback index context mismatch"
            else Right ()
          validateDiagram inner
          innerDom <- mapM (requirePortType inner) (dIn inner)
          innerCod <- mapM (requirePortType inner) (dOut inner)
          case (innerDom, innerCod) of
            ([stateIn], stateOut : codTail) -> do
              if stateIn /= stateOut
                then Left "validateDiagram: feedback body first output must match input type"
                else Right ()
              if stateIn /= fbTy spec
                then Left "validateDiagram: feedback state type mismatch"
                else Right ()
              if length codTail /= fbOutArity spec
                then Left "validateDiagram: feedback output arity mismatch"
                else Right ()
              outerDom <- mapM (requirePortType diag) (eIns edge)
              outerCod <- mapM (requirePortType diag) (eOuts edge)
              if null outerDom
                then Right ()
                else Left "validateDiagram: feedback edge must not consume outer inputs"
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
          let prodKeep = IM.lookup (portKey keep) (dProd diag)
          let prodDrop = IM.lookup (portKey drop) (dProd diag)
          let consKeep = IM.lookup (portKey keep) (dCons diag)
          let consDrop = IM.lookup (portKey drop) (dCons diag)
          prod <- mergeEndpoint "producer" prodKeep prodDrop
          cons <- mergeEndpoint "consumer" consKeep consDrop
          let diag' = diag
                { dPortTy = IM.delete (portKey drop) (dPortTy diag)
                , dPortLabel =
                    IM.insert
                      (portKey keep)
                      (mergeLabel labelKeep labelDrop)
                      (IM.delete (portKey drop) (dPortLabel diag))
                , dProd = IM.insert (portKey keep) prod (IM.delete (portKey drop) (dProd diag))
                , dCons = IM.insert (portKey keep) cons (IM.delete (portKey drop) (dCons diag))
                , dIn = replacePort keep drop (dIn diag)
                , dOut = replacePort keep drop (dOut diag)
                , dEdges = IM.map (mergeEdge keep drop) (dEdges diag)
                }
          pure diag'
  where
    requireType pid =
      case IM.lookup (portKey pid) (dPortTy diag) of
        Nothing -> Left "mergePorts: missing port"
        Just ty -> Right ty
    requireLabel pid =
      case IM.lookup (portKey pid) (dPortLabel diag) of
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

dedupe :: Ord a => [a] -> [a]
dedupe = go S.empty
  where
    go _ [] = []
    go seen (x:xs)
      | x `S.member` seen = go seen xs
      | otherwise = x : go (S.insert x seen) xs

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
          PFeedback spec inner -> PFeedback spec (shiftDiagram portOff edgeOff inner)
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
    sortPorts = map PortId . IM.keys . IM.fromList . map (\p -> (portKey p, ()))
    assignEdges d =
      let edges = IM.elems (dEdges d)
          edgesSorted = sortEdges edges
          mp = foldl (\m (i, e) -> M.insert (eId e) (EdgeId i) m) M.empty (zip [0..] edgesSorted)
      in mp
    sortEdges = map snd . M.toAscList . M.fromList . map (\e -> (edgeKey (eId e), e))
    buildPortMap mp portMap =
      fmap IM.fromList $
        mapM
          (\(k, ty) -> do
            p <- requirePort mp (PortId k)
            pure (portKey p, ty))
          (IM.toList portMap)
    buildEdgeRefMap mp em refMap =
      fmap IM.fromList $
        mapM
          (\(k, edgeRef) -> do
            p <- requirePort mp (PortId k)
            edgeRef' <- traverse (requireEdge em) edgeRef
            pure (portKey p, edgeRef'))
          (IM.toList refMap)
    buildEdges mp em edges =
      fmap IM.fromList $
        mapM
          (\edge -> do
            eid <- requireEdge em (eId edge)
            ins <- mapM (requirePort mp) (eIns edge)
            outs <- mapM (requirePort mp) (eOuts edge)
            payload <- mapPayload (ePayload edge)
            pure (edgeKey eid, edge { eId = eid, ePayload = payload, eIns = ins, eOuts = outs }))
          (IM.elems edges)
    mapPayload payload =
      case payload of
        PGen g attrs bargs -> do
          bargs' <- mapM mapBinderArg bargs
          Right (PGen g attrs bargs')
        PBox name inner -> do
          inner' <- renumberDiagram inner
          Right (PBox name inner')
        PFeedback spec inner -> do
          inner' <- renumberDiagram inner
          Right (PFeedback spec inner')
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
diagramIsoEq left right
  | dMode left /= dMode right = Right False
  | dIxCtx left /= dIxCtx right = Right False
  | length (dIn left) /= length (dIn right) = Right False
  | length (dOut left) /= length (dOut right) = Right False
  | IM.size (dPortTy left) /= IM.size (dPortTy right) = Right False
  | IM.size (dEdges left) /= IM.size (dEdges right) = Right False
  | otherwise = do
      let initPairs = zip (dIn left) (dIn right) <> zip (dOut left) (dOut right)
      st0 <- foldl addInit (Right emptyState) initPairs
      isoSearch st0
  where
    emptyState = IsoState M.empty M.empty S.empty S.empty []
    addInit acc (p1, p2) = do
      st <- acc
      addPortPair st p1 p2
    isoSearch st = do
      st' <- propagate st
      if M.size (isEdgeMap st') == IM.size (dEdges left) && M.size (isPortMap st') == IM.size (dPortTy left)
        then Right True
        else do
          case nextUnmappedEdge st' of
            Nothing -> Right False
            Just e1 -> do
              let candidates = filter (edgeCompatible e1) (unmappedEdges st')
              tryCandidates st' e1 candidates
    tryCandidates _ _ [] = Right False
    tryCandidates st e1 (e2:rest) = do
      case tryMapEdge st e1 e2 of
        Left _ -> tryCandidates st e1 rest
        Right st' -> do
          ok <- isoSearch st'
          if ok then Right True else tryCandidates st e1 rest

    propagate st0 =
      case isQueue st0 of
        [] -> Right st0
        ((p1, p2):rest) -> do
          st1 <- checkPortTypes st0 p1 p2
          st2 <- mapIncidentEdges st1 p1 p2
          propagate st2 { isQueue = rest }

    checkPortTypes st p1 p2 = do
      ty1 <- requirePortType left p1
      ty2 <- requirePortType right p2
      if ty1 == ty2
        then Right st
        else Left "diagramIsoEq: port type mismatch"

    mapIncidentEdges st p1 p2 = do
      st1 <- mapEndpoint "producer" (lookupEdge left (dProd left) p1) (lookupEdge right (dProd right) p2) st
      mapEndpoint "consumer" (lookupEdge left (dCons left) p1) (lookupEdge right (dCons right) p2) st1

    mapEndpoint _ Nothing Nothing st = Right st
    mapEndpoint _ (Just e1) (Just e2) st = addEdgePair st e1 e2
    mapEndpoint label _ _ _ = Left ("diagramIsoEq: " <> label <> " incidence mismatch")

    lookupEdge diag mp pid =
      case IM.lookup (portKey pid) mp of
        Just (Just eid) -> IM.lookup (edgeKey eid) (dEdges diag)
        Just Nothing -> Nothing
        Nothing -> Nothing

    addPortPair st p1 p2 =
      case M.lookup p1 (isPortMap st) of
        Just mapped ->
          if mapped == p2 then Right st else Left "diagramIsoEq: port mapping conflict"
        Nothing ->
          if p2 `S.member` isUsedPorts st
            then Left "diagramIsoEq: target port already used"
            else Right st
              { isPortMap = M.insert p1 p2 (isPortMap st)
              , isUsedPorts = S.insert p2 (isUsedPorts st)
              , isQueue = isQueue st <> [(p1, p2)]
              }

    addEdgePair st e1 e2 =
      case M.lookup (eId e1) (isEdgeMap st) of
        Just mapped ->
          if mapped == eId e2 then Right st else Left "diagramIsoEq: edge mapping conflict"
        Nothing ->
          if eId e2 `S.member` isUsedEdges st
            then Left "diagramIsoEq: target edge already used"
            else do
              ensureEdgeCompatible e1 e2
              st' <- foldl addPort (Right st
                { isEdgeMap = M.insert (eId e1) (eId e2) (isEdgeMap st)
                , isUsedEdges = S.insert (eId e2) (isUsedEdges st)
                }) (zip (eIns e1) (eIns e2) <> zip (eOuts e1) (eOuts e2))
              pure st'
      where
        addPort acc (p1, p2) = do
          st' <- acc
          addPortPair st' p1 p2

    ensureEdgeCompatible e1 e2 = do
      if length (eIns e1) /= length (eIns e2) || length (eOuts e1) /= length (eOuts e2)
        then Left "diagramIsoEq: edge arity mismatch"
        else payloadCompatible (ePayload e1) (ePayload e2)

    payloadCompatible p1 p2 =
      case (p1, p2) of
        (PGen g1 attrs1 bargs1, PGen g2 attrs2 bargs2) ->
          if g1 == g2 && attrs1 == attrs2 && length bargs1 == length bargs2
            then do
              okArgs <- and <$> mapM binderArgCompatible (zip bargs1 bargs2)
              if okArgs then Right () else Left "diagramIsoEq: binder argument mismatch"
            else Left "diagramIsoEq: generator mismatch"
        (PBox _ d1, PBox _ d2) -> do
          ok <- diagramIsoEq d1 d2
          if ok then Right () else Left "diagramIsoEq: box diagram mismatch"
        (PFeedback spec1 d1, PFeedback spec2 d2) ->
          if spec1 /= spec2
            then Left "diagramIsoEq: feedback spec mismatch"
            else do
              ok <- diagramIsoEq d1 d2
              if ok then Right () else Left "diagramIsoEq: feedback body mismatch"
        (PSplice x, PSplice y) ->
          if x == y
            then Right ()
            else Left "diagramIsoEq: splice variable mismatch"
        _ -> Left "diagramIsoEq: payload mismatch"

    binderArgCompatible (a, b) =
      case (a, b) of
        (BAConcrete d1, BAConcrete d2) -> diagramIsoEq d1 d2
        (BAMeta x, BAMeta y) -> Right (x == y)
        _ -> Right False

    requirePortType diag pid =
      case diagramPortType diag pid of
        Nothing -> Left "diagramIsoEq: missing port type"
        Just ty -> Right ty

    nextUnmappedEdge st =
      let candidates = filter (\e -> M.notMember (eId e) (isEdgeMap st)) (IM.elems (dEdges left))
      in case candidates of
        [] -> Nothing
        _ -> Just (head candidates)

    unmappedEdges st =
      [ e
      | e <- IM.elems (dEdges right)
      , eId e `S.notMember` isUsedEdges st
      ]

    edgeCompatible e1 e2 =
      case ensureEdgeCompatible e1 e2 of
        Right _ -> True
        Left _ -> False

    tryMapEdge st e1 e2 = addEdgePair st e1 e2

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
diagramIsoMatchWithVars tt tyFlex ixFlex attrFlex left right
  | dMode left /= dMode right = Right []
  | dIxCtx left /= dIxCtx right = Right []
  | length (dIn left) /= length (dIn right) = Right []
  | length (dOut left) /= length (dOut right) = Right []
  | IM.size (dPortTy left) /= IM.size (dPortTy right) = Right []
  | IM.size (dEdges left) /= IM.size (dEdges right) = Right []
  | otherwise = do
      let initPairs = zip (dIn left) (dIn right) <> zip (dOut left) (dOut right)
      st0 <- foldl addInit (Right (Just emptyState)) initPairs
      case st0 of
        Nothing -> Right []
        Just st -> fmap (map (\s -> (imsTySubst s, imsAttrSubst s))) (isoSearch st)
  where
    emptyState = IsoMatchState M.empty M.empty S.empty S.empty [] emptySubst M.empty

    addInit acc (p1, p2) = do
      mSt <- acc
      case mSt of
        Nothing -> Right Nothing
        Just st ->
          case addPortPair st p1 p2 of
            Nothing -> Right Nothing
            Just st' -> Right (Just st')

    isoSearch st = do
      states <- propagate st
      fmap concat (mapM expand states)

    expand st =
      if M.size (imsEdgeMap st) == IM.size (dEdges left) && M.size (imsPortMap st) == IM.size (dPortTy left)
        then Right [st]
        else do
          case nextUnmappedEdge st of
            Nothing -> Right []
            Just e1 -> do
              let candidates = filter (edgeCompatible e1) (unmappedEdges st)
              fmap concat (mapM (tryCandidate st e1) candidates)

    tryCandidate st e1 e2 = do
      states <- tryMapEdge st e1 e2
      fmap concat (mapM isoSearch states)

    propagate st0 =
      case imsQueue st0 of
        [] -> Right [st0]
        ((p1, p2):rest) -> do
          let stBase = st0 { imsQueue = rest }
          st1s <- checkPortTypes stBase p1 p2
          st2s <- fmap concat (mapM (mapIncidentEdges p1 p2) st1s)
          fmap concat (mapM propagate st2s)

    checkPortTypes st p1 p2 = do
      ty1 <- requirePortType left p1
      ty2 <- requirePortType right p2
      let subst = imsTySubst st
      case (applySubstTy tt subst ty1, applySubstTy tt subst ty2) of
        (Right ty1', Right ty2') ->
          case unifyTyFlex tt (dIxCtx left) tyFlex ixFlex emptySubst ty1' ty2' of
            Left _ -> Right []
            Right s1 ->
              case composeSubst tt s1 subst of
                Left _ -> Right []
                Right subst' ->
                  Right [st { imsTySubst = subst' }]
        _ -> Right []

    mapIncidentEdges p1 p2 st = do
      st1s <- mapEndpoint "producer" (lookupEdge left (dProd left) p1) (lookupEdge right (dProd right) p2) st
      fmap concat (mapM (mapEndpoint "consumer" (lookupEdge left (dCons left) p1) (lookupEdge right (dCons right) p2)) st1s)

    mapEndpoint _ Nothing Nothing st = Right [st]
    mapEndpoint _ (Just e1) (Just e2) st = addEdgePair st e1 e2
    mapEndpoint _ _ _ _ = Right []

    lookupEdge diag mp pid =
      case IM.lookup (portKey pid) mp of
        Just (Just eid) -> IM.lookup (edgeKey eid) (dEdges diag)
        Just Nothing -> Nothing
        Nothing -> Nothing

    addPortPair st p1 p2 =
      case M.lookup p1 (imsPortMap st) of
        Just mapped ->
          if mapped == p2 then Just st else Nothing
        Nothing ->
          if p2 `S.member` imsUsedPorts st
            then Nothing
            else Just st
              { imsPortMap = M.insert p1 p2 (imsPortMap st)
              , imsUsedPorts = S.insert p2 (imsUsedPorts st)
              , imsQueue = imsQueue st <> [(p1, p2)]
              }

    addEdgePair st e1 e2 =
      case M.lookup (eId e1) (imsEdgeMap st) of
        Just mapped ->
          if mapped == eId e2 then Right [st] else Right []
        Nothing ->
          if eId e2 `S.member` imsUsedEdges st
            then Right []
            else do
              subs <- payloadSubsts st (ePayload e1) (ePayload e2)
              fmap concat (mapM (attachEdge st e1 e2) subs)

    attachEdge st e1 e2 (tySubst, attrSubst) = do
      if length (eIns e1) /= length (eIns e2) || length (eOuts e1) /= length (eOuts e2)
        then Right []
        else do
          let st0 = st
                { imsEdgeMap = M.insert (eId e1) (eId e2) (imsEdgeMap st)
                , imsUsedEdges = S.insert (eId e2) (imsUsedEdges st)
                , imsTySubst = tySubst
                , imsAttrSubst = attrSubst
                }
          foldl addPorts (Right [st0]) (zip (eIns e1) (eIns e2) <> zip (eOuts e1) (eOuts e2))
      where
        addPorts acc (p1, p2) = do
          states <- acc
          pure [ st'' | st' <- states, Just st'' <- [addPortPair st' p1 p2] ]

    payloadSubsts st p1 p2 =
      case (p1, p2) of
        (PGen g1 attrs1 bargs1, PGen g2 attrs2 bargs2) ->
          if g1 /= g2 || M.keysSet attrs1 /= M.keysSet attrs2 || length bargs1 /= length bargs2
            then Right []
            else do
              let attrSubst0 = imsAttrSubst st
              case foldl unifyField (Right attrSubst0) (M.toList attrs1) of
                Left _ -> Right []
                Right attrSubst' ->
                  foldl step (Right [(imsTySubst st, attrSubst')]) (zip bargs1 bargs2)
          where
            unifyField acc (field, term1) = do
              sub <- acc
              case M.lookup field attrs2 of
                Nothing -> Left "diagramIsoMatchWithVars: missing attribute field"
                Just term2 -> unifyAttrFlex attrFlex sub term1 term2
            step acc pair = do
              subs <- acc
              fmap concat (mapM (\(tyS, attrS) -> binderArgSubsts tyS attrS pair) subs)

            binderArgSubsts tySubst0 attrSubst0 (lhsArg, rhsArg) =
              case (lhsArg, rhsArg) of
                (BAConcrete d1, BAConcrete d2) ->
                  case (applySubstsDiagramLocal tt tySubst0 attrSubst0 d1, applySubstsDiagramLocal tt tySubst0 attrSubst0 d2) of
                    (Right d1', Right d2') ->
                      case diagramIsoMatchWithVars tt tyFlex ixFlex attrFlex d1' d2' of
                        Left _ -> Right []
                        Right subs ->
                          fmap concat
                            ( mapM
                                (\(tySub, attrSub) ->
                                  case composeSubst tt tySub tySubst0 of
                                    Left _ -> Right []
                                    Right tySub' -> Right [(tySub', composeAttrSubst attrSub attrSubst0)]
                                )
                                subs
                            )
                    _ -> Right []
                (BAMeta x, BAMeta y) ->
                  if x == y then Right [(tySubst0, attrSubst0)] else Right []
                _ -> Right []
        (PBox _ d1, PBox _ d2) -> do
          let tySubst = imsTySubst st
          let attrSubst = imsAttrSubst st
          case (applySubstsDiagramLocal tt tySubst attrSubst d1, applySubstsDiagramLocal tt tySubst attrSubst d2) of
            (Right d1', Right d2') ->
              case diagramIsoMatchWithVars tt tyFlex ixFlex attrFlex d1' d2' of
                Left _ -> Right []
                Right subs ->
                  fmap concat
                    ( mapM
                        (\(tySub, attrSub) ->
                          case composeSubst tt tySub tySubst of
                            Left _ -> Right []
                            Right tySub' -> Right [(tySub', composeAttrSubst attrSub attrSubst)]
                        )
                        subs
                    )
            _ -> Right []
        (PFeedback spec1 d1, PFeedback spec2 d2) ->
          if spec1 /= spec2
            then Right []
            else do
              let tySubst = imsTySubst st
              let attrSubst = imsAttrSubst st
              case (applySubstsDiagramLocal tt tySubst attrSubst d1, applySubstsDiagramLocal tt tySubst attrSubst d2) of
                (Right d1', Right d2') ->
                  case diagramIsoMatchWithVars tt tyFlex ixFlex attrFlex d1' d2' of
                    Left _ -> Right []
                    Right subs ->
                      fmap concat
                        ( mapM
                            (\(tySub, attrSub) ->
                              case composeSubst tt tySub tySubst of
                                Left _ -> Right []
                                Right tySub' -> Right [(tySub', composeAttrSubst attrSub attrSubst)]
                            )
                            subs
                        )
                _ -> Right []
        (PSplice x, PSplice y) ->
          if x == y then Right [(imsTySubst st, imsAttrSubst st)] else Right []
        _ -> Right []

    requirePortType diag pid =
      case diagramPortType diag pid of
        Nothing -> Left "diagramIsoMatchWithVars: missing port type"
        Just ty -> Right ty

    nextUnmappedEdge st =
      let candidates = filter (\e -> M.notMember (eId e) (imsEdgeMap st)) (IM.elems (dEdges left))
      in case candidates of
        [] -> Nothing
        _ -> Just (head candidates)

    unmappedEdges st =
      [ e
      | e <- IM.elems (dEdges right)
      , eId e `S.notMember` imsUsedEdges st
      ]

    edgeCompatible e1 e2 =
      length (eIns e1) == length (eIns e2)
        && length (eOuts e1) == length (eOuts e2)
        && payloadCompatible (ePayload e1) (ePayload e2)

    payloadCompatible p1 p2 =
      case (p1, p2) of
        (PGen g1 attrs1 bargs1, PGen g2 attrs2 bargs2) ->
          g1 == g2 && M.keysSet attrs1 == M.keysSet attrs2 && length bargs1 == length bargs2
        (PBox _ _, PBox _ _) -> True
        (PFeedback spec1 _, PFeedback spec2 _) -> spec1 == spec2
        (PSplice x, PSplice y) -> x == y
        _ -> False

    tryMapEdge st e1 e2 = addEdgePair st e1 e2

applySubstsDiagramLocal :: TypeTheory -> Subst -> AttrSubst -> Diagram -> Either Text Diagram
applySubstsDiagramLocal tt tySubst attrSubst diag = do
  dPortTy' <- traverse (applySubstTy tt tySubst) (dPortTy diag)
  dIxCtx' <- mapM (applySubstTy tt tySubst) (dIxCtx diag)
  dEdges' <- traverse (mapEdgePayloadLocal tySubst attrSubst) (dEdges diag)
  pure diag { dIxCtx = dIxCtx', dPortTy = dPortTy', dEdges = dEdges' }
  where
    mapEdgePayloadLocal tyS attrS edge =
      case ePayload edge of
        PGen g attrs bargs -> do
          bargs' <- mapM (mapBinderArg tyS attrS) bargs
          Right (edge { ePayload = PGen g (applyAttrSubstMap attrS attrs) bargs' })
        PBox name inner -> do
          inner' <- applySubstsDiagramLocal tt tyS attrS inner
          Right (edge { ePayload = PBox name inner' })
        PFeedback spec inner -> do
          specTy' <- applySubstTy tt tyS (fbTy spec)
          inner' <- applySubstsDiagramLocal tt tyS attrS inner
          Right (edge { ePayload = PFeedback spec { fbTy = specTy' } inner' })
        PSplice x -> Right (edge { ePayload = PSplice x })

    mapBinderArg tyS attrS barg =
      case barg of
        BAConcrete inner -> BAConcrete <$> applySubstsDiagramLocal tt tyS attrS inner
        BAMeta x -> Right (BAMeta x)
