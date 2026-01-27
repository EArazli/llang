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
  , canonicalizeDiagram
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
import Strat.Poly.ModeTheory (ModeName)
import Strat.Poly.TypeExpr (TypeExpr)
import Strat.Poly.Names (GenName(..), BoxName(..))


newtype PortId = PortId Int deriving (Eq, Ord, Show)
newtype EdgeId = EdgeId Int deriving (Eq, Ord, Show)

data EdgePayload
  = PGen GenName
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
  addEdgePayload (PGen gen) ins outs diag

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
  mapM_ (ensurePortExists diag) (dIn diag)
  mapM_ (ensurePortExists diag) (dOut diag)
  mapM_ checkEdge (IM.elems (dEdges diag))
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
        PGen _ -> Right ()
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
          PGen g -> PGen g
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

canonicalizeDiagram :: Diagram -> Either Text Diagram
canonicalizeDiagram diag = do
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
        PGen g -> Right (PGen g)
        PBox name inner -> do
          inner' <- canonicalizeDiagram inner
          Right (PBox name inner')
    requirePort mp pid =
      case M.lookup pid mp of
        Nothing -> Left "canonicalizeDiagram: missing port mapping"
        Just v -> Right v
    requireEdge mp eid =
      case M.lookup eid mp of
        Nothing -> Left "canonicalizeDiagram: missing edge mapping"
        Just v -> Right v

unionDisjointIntMap :: Text -> IM.IntMap a -> IM.IntMap a -> Either Text (IM.IntMap a)
unionDisjointIntMap label left right =
  let ksL = IM.keysSet left
      ksR = IM.keysSet right
      overlap = IS.toList (IS.intersection ksL ksR)
  in if null overlap
    then Right (IM.union left right)
    else Left (label <> ": key collision " <> T.pack (show overlap))
