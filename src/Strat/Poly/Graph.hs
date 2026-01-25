{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Graph
  ( PortId(..)
  , EdgeId(..)
  , Edge(..)
  , Diagram(..)
  , emptyDiagram
  , freshPort
  , addEdge
  , validateDiagram
  , mergePorts
  , canonicalizeDiagram
  , shiftDiagram
  , diagramPortType
  , diagramPortIds
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.IntMap.Strict as IM
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import Strat.Poly.ModeTheory (ModeName)
import Strat.Poly.TypeExpr (TypeExpr)
import Strat.Poly.Names (GenName(..))


newtype PortId = PortId Int deriving (Eq, Ord, Show)
newtype EdgeId = EdgeId Int deriving (Eq, Ord, Show)

data Edge = Edge
  { eId   :: EdgeId
  , eGen  :: GenName
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
addEdge gen ins outs diag = do
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
  let edge = Edge { eId = eid, eGen = gen, eIns = ins, eOuts = outs }
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
  mapM_ (ensurePortExists diag) (dIn diag)
  mapM_ (ensurePortExists diag) (dOut diag)
  mapM_ checkEdge (IM.elems (dEdges diag))
  mapM_ checkIncidence (IM.keys (dPortTy diag))
  pure ()
  where
    checkEdge edge = do
      mapM_ (ensurePortExists diag) (eIns edge <> eOuts edge)
      mapM_ (checkCons edge) (eIns edge)
      mapM_ (checkProd edge) (eOuts edge)
    checkCons edge pid =
      case IM.lookup (portKey pid) (dCons diag) of
        Just (Just eid) | eid == eId edge -> Right ()
        _ -> Left "validateDiagram: consumer incidence mismatch"
    checkProd edge pid =
      case IM.lookup (portKey pid) (dProd diag) of
        Just (Just eid) | eid == eId edge -> Right ()
        _ -> Left "validateDiagram: producer incidence mismatch"
    checkIncidence k =
      case (IM.lookup k (dProd diag), IM.lookup k (dCons diag)) of
        (Just _, Just _) -> Right ()
        _ -> Left "validateDiagram: missing incidence entry"

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
          , eIns = shiftPorts (eIns edge)
          , eOuts = shiftPorts (eOuts edge)
          }
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

canonicalizeDiagram :: Diagram -> Diagram
canonicalizeDiagram diag =
  let (portMap, nextPort) = assignPorts diag
      edgeMap = assignEdges diag
      mapPort pid =
        case M.lookup pid portMap of
          Nothing -> error "canonicalizeDiagram: missing port mapping"
          Just p -> p
      mapEdge eid =
        case M.lookup eid edgeMap of
          Nothing -> error "canonicalizeDiagram: missing edge mapping"
          Just e -> e
      dPortTy' =
        IM.fromList
          [ (portKey (mapPort (PortId k)), ty)
          | (k, ty) <- IM.toList (dPortTy diag)
          ]
      dProd' =
        IM.fromList
          [ (portKey (mapPort (PortId k)), fmap mapEdge edge)
          | (k, edge) <- IM.toList (dProd diag)
          ]
      dCons' =
        IM.fromList
          [ (portKey (mapPort (PortId k)), fmap mapEdge edge)
          | (k, edge) <- IM.toList (dCons diag)
          ]
      dEdges' =
        IM.fromList
          [ (edgeKey (mapEdge (eId edge)), edge { eId = mapEdge (eId edge), eIns = map mapPort (eIns edge), eOuts = map mapPort (eOuts edge) })
          | edge <- IM.elems (dEdges diag)
          ]
  in Diagram
      { dMode = dMode diag
      , dIn = map mapPort (dIn diag)
      , dOut = map mapPort (dOut diag)
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
