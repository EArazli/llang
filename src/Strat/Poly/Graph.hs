{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Graph
  ( PortId(..)
  , EdgeId(..)
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
  , diagramPortIds
  , unionDisjointIntMap
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import Strat.Poly.ModeTheory (ModeName(..), ModeTheory)
import Strat.Poly.TypeExpr (TypeExpr, TyVar, typeMode)
import Strat.Poly.Names (GenName(..), BoxName(..))
import Strat.Poly.UnifyTy (Subst, unifyTyFlex, applySubstTy, composeSubst)
import Strat.Poly.Attr (AttrMap, AttrSubst, AttrVar, applyAttrSubstMap, composeAttrSubst, unifyAttrFlex)
import Strat.Poly.TypePretty (renderType)


newtype PortId = PortId Int deriving (Eq, Ord, Show)
newtype EdgeId = EdgeId Int deriving (Eq, Ord, Show)

data EdgePayload
  = PGen GenName AttrMap
  | PBox BoxName Diagram
  deriving (Eq, Ord, Show)

data Edge = Edge
  { eId   :: EdgeId
  , ePayload :: EdgePayload
  , eIns  :: [PortId]
  , eOuts :: [PortId]
  } deriving (Eq, Ord, Show)

data Diagram = Diagram
  { dMode     :: ModeName
  , dIn       :: [PortId]
  , dOut      :: [PortId]
  , dPortTy   :: IM.IntMap TypeExpr
  , dProd     :: IM.IntMap (Maybe EdgeId)
  , dCons     :: IM.IntMap (Maybe EdgeId)
  , dEdges    :: IM.IntMap Edge
  , dNextPort :: Int
  , dNextEdge :: Int
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


emptyDiagram :: ModeName -> Diagram
emptyDiagram mode = Diagram
  { dMode = mode
  , dIn = []
  , dOut = []
  , dPortTy = IM.empty
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

freshPort :: TypeExpr -> Diagram -> (PortId, Diagram)
freshPort ty diag =
  let pid = PortId (dNextPort diag)
      k = portKey pid
      diag' = diag
        { dPortTy = IM.insert k ty (dPortTy diag)
        , dProd = IM.insert k Nothing (dProd diag)
        , dCons = IM.insert k Nothing (dCons diag)
        , dNextPort = dNextPort diag + 1
        }
  in (pid, diag')

addEdge :: GenName -> [PortId] -> [PortId] -> Diagram -> Either Text Diagram
addEdge gen ins outs diag =
  addEdgePayload (PGen gen M.empty) ins outs diag

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
      let ksTy = IM.keysSet (dPortTy diag)
          ksProd = IM.keysSet (dProd diag)
          ksCons = IM.keysSet (dCons diag)
      in if ksTy == ksProd && ksTy == ksCons
        then Right ()
        else Left "validateDiagram: port map keysets mismatch"
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
        PGen _ _ -> Right ()
        PBox _ inner -> do
          if dMode inner /= dMode diag
            then Left "validateDiagram: box mode mismatch"
            else Right ()
          validateDiagram inner
          domOuter <- mapM (requirePortType diag) (eIns edge)
          codOuter <- mapM (requirePortType diag) (eOuts edge)
          domInner <- mapM (requirePortType inner) (dIn inner)
          codInner <- mapM (requirePortType inner) (dOut inner)
          if domOuter == domInner && codOuter == codInner
            then Right ()
            else Left "validateDiagram: box boundary mismatch"
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
        then Right ()
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
          PGen g attrs -> PGen g attrs
          PBox name inner -> PBox name (shiftDiagram portOff edgeOff inner)
      shiftPortMap = IM.mapKeysMonotonic (+ portOff)
      shiftEdgeMap = IM.mapKeysMonotonic (+ edgeOff)
  in diag
      { dIn = shiftPorts (dIn diag)
      , dOut = shiftPorts (dOut diag)
      , dPortTy = shiftPortMap (dPortTy diag)
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
  dProd' <- buildEdgeRefMap portMap edgeMap (dProd diag)
  dCons' <- buildEdgeRefMap portMap edgeMap (dCons diag)
  dEdges' <- buildEdges portMap edgeMap (dEdges diag)
  dIn' <- mapM (requirePort portMap) (dIn diag)
  dOut' <- mapM (requirePort portMap) (dOut diag)
  pure Diagram
    { dMode = dMode diag
    , dIn = dIn'
    , dOut = dOut'
    , dPortTy = dPortTy'
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
        PGen g attrs -> Right (PGen g attrs)
        PBox name inner -> do
          inner' <- renumberDiagram inner
          Right (PBox name inner')
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
        (PGen g1 attrs1, PGen g2 attrs2) ->
          if g1 == g2 && attrs1 == attrs2
            then Right ()
            else Left "diagramIsoEq: generator mismatch"
        (PBox _ d1, PBox _ d2) -> do
          ok <- diagramIsoEq d1 d2
          if ok then Right () else Left "diagramIsoEq: box diagram mismatch"
        _ -> Left "diagramIsoEq: payload mismatch"

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
  :: ModeTheory
  -> S.Set TyVar
  -> S.Set AttrVar
  -> Diagram
  -> Diagram
  -> Either Text [(Subst, AttrSubst)]
diagramIsoMatchWithVars mt tyFlex attrFlex left right
  | dMode left /= dMode right = Right []
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
    emptyState = IsoMatchState M.empty M.empty S.empty S.empty [] M.empty M.empty

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
      case unifyTyFlex mt tyFlex (applySubstTy mt subst ty1) (applySubstTy mt subst ty2) of
        Left _ -> Right []
        Right s1 ->
          let subst' = composeSubst mt s1 subst
          in Right [st { imsTySubst = subst' }]

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
        (PGen g1 attrs1, PGen g2 attrs2) ->
          if g1 /= g2 || M.keysSet attrs1 /= M.keysSet attrs2
            then Right []
            else do
              let attrSubst0 = imsAttrSubst st
              case foldl unifyField (Right attrSubst0) (M.toList attrs1) of
                Left _ -> Right []
                Right attrSubst' -> Right [(imsTySubst st, attrSubst')]
          where
            unifyField acc (field, term1) = do
              sub <- acc
              case M.lookup field attrs2 of
                Nothing -> Left "diagramIsoMatchWithVars: missing attribute field"
                Just term2 -> unifyAttrFlex attrFlex sub term1 term2
        (PBox _ d1, PBox _ d2) -> do
          let tySubst = imsTySubst st
          let attrSubst = imsAttrSubst st
          let d1' = applySubstsDiagramLocal mt tySubst attrSubst d1
          let d2' = applySubstsDiagramLocal mt tySubst attrSubst d2
          case diagramIsoMatchWithVars mt tyFlex attrFlex d1' d2' of
            Left _ -> Right []
            Right subs ->
              Right
                [ (composeSubst mt tySub tySubst, composeAttrSubst attrSub attrSubst)
                | (tySub, attrSub) <- subs
                ]
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
        (PGen g1 attrs1, PGen g2 attrs2) ->
          g1 == g2 && M.keysSet attrs1 == M.keysSet attrs2
        (PBox _ _, PBox _ _) -> True
        _ -> False

    tryMapEdge st e1 e2 = addEdgePair st e1 e2

applySubstsDiagramLocal :: ModeTheory -> Subst -> AttrSubst -> Diagram -> Diagram
applySubstsDiagramLocal mt tySubst attrSubst diag =
  let dPortTy' = IM.map (applySubstTy mt tySubst) (dPortTy diag)
      dEdges' = IM.map (mapEdgePayloadLocal tySubst attrSubst) (dEdges diag)
  in diag { dPortTy = dPortTy', dEdges = dEdges' }
  where
    mapEdgePayloadLocal tyS attrS edge =
      case ePayload edge of
        PGen g attrs ->
          edge { ePayload = PGen g (applyAttrSubstMap attrS attrs) }
        PBox name inner ->
          edge { ePayload = PBox name (applySubstsDiagramLocal mt tyS attrS inner) }
