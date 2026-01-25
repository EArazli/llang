{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Match
  ( Match(..)
  , findFirstMatch
  , findAllMatches
  , findFirstMatchNoDoc
  , findAllMatchesNoDoc
  ) where

import Data.Text (Text)
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import qualified Data.Set as S
import Data.List (sortOn)
import Strat.Poly.Graph
import Strat.Poly.Doctrine (Doctrine)
import Strat.Poly.TypeExpr (TypeExpr)
import Strat.Poly.UnifyTy


data Match = Match
  { mPorts :: M.Map PortId PortId
  , mEdges :: M.Map EdgeId EdgeId
  , mTySub :: Subst
  } deriving (Eq, Show)

findFirstMatch :: Doctrine -> Diagram -> Diagram -> Either Text (Maybe Match)
findFirstMatch _ lhs host = do
  matches <- findAllMatchesInternal lhs host
  pure (case matches of
          [] -> Nothing
          (m:_) -> Just m)

findAllMatches :: Doctrine -> Diagram -> Diagram -> Either Text [Match]
findAllMatches _ lhs host = findAllMatchesInternal lhs host

findFirstMatchNoDoc :: Diagram -> Diagram -> Either Text (Maybe Match)
findFirstMatchNoDoc lhs host = do
  matches <- findAllMatchesInternal lhs host
  pure (case matches of
          [] -> Nothing
          (m:_) -> Just m)

findAllMatchesNoDoc :: Diagram -> Diagram -> Either Text [Match]
findAllMatchesNoDoc = findAllMatchesInternal

findAllMatchesInternal :: Diagram -> Diagram -> Either Text [Match]
findAllMatchesInternal lhs host = do
  let lhsEdges = IM.elems (dEdges lhs)
  let hostEdges = IM.elems (dEdges host)
  let adj = adjacency lhs
  let allEdgeIds = map eId lhsEdges
  go [] (Match M.empty M.empty M.empty) adj allEdgeIds lhsEdges hostEdges
  where
    go acc match adj allEdgeIds lhsEdges hostEdges =
      case pickNextEdge match adj allEdgeIds of
        Nothing ->
          if danglingOk lhs host match
            then Right (acc <> [match])
            else Right acc
        Just eid -> do
          let edge = lookupEdge lhs eid
          let candidates = filter (edgeCompatible match edge) hostEdges
          tryCandidates acc match adj allEdgeIds edge candidates
    tryCandidates acc match adj allEdgeIds edge [] = Right acc
    tryCandidates acc match adj allEdgeIds edge (cand:cands) = do
      case extendMatch lhs host match edge cand of
        Left _ -> tryCandidates acc match adj allEdgeIds edge cands
        Right match' -> do
          acc' <- go acc match' adj allEdgeIds (IM.elems (dEdges lhs)) (IM.elems (dEdges host))
          tryCandidates acc' match adj allEdgeIds edge cands

lookupEdge :: Diagram -> EdgeId -> Edge
lookupEdge diag eid =
  case IM.lookup (edgeKey eid) (dEdges diag) of
    Nothing -> error "match: missing edge id"
    Just e -> e
  where
    edgeKey (EdgeId k) = k

edgeCompatible :: Match -> Edge -> Edge -> Bool
edgeCompatible match pat host =
  eGen pat == eGen host
    && length (eIns pat) == length (eIns host)
    && length (eOuts pat) == length (eOuts host)
    && portsCompatible match (eIns pat) (eIns host)
    && portsCompatible match (eOuts pat) (eOuts host)

portsCompatible :: Match -> [PortId] -> [PortId] -> Bool
portsCompatible match pats hosts =
  and (zipWith ok pats hosts)
  where
    ok p h =
      case M.lookup p (mPorts match) of
        Nothing -> True
        Just h' -> h' == h

extendMatch :: Diagram -> Diagram -> Match -> Edge -> Edge -> Either Text Match
extendMatch lhs host match patEdge hostEdge = do
  if M.member (eId patEdge) (mEdges match)
    then Left "extendMatch: edge already mapped"
    else do
      let pairs = zip (eIns patEdge <> eOuts patEdge) (eIns hostEdge <> eOuts hostEdge)
      (portMap, subst) <- foldl step (Right (mPorts match, mTySub match)) pairs
      let edgeMap = M.insert (eId patEdge) (eId hostEdge) (mEdges match)
      pure match { mPorts = portMap, mEdges = edgeMap, mTySub = subst }
  where
    step acc (p, h) = do
      (portMap, subst) <- acc
      case M.lookup p portMap of
        Just h' ->
          if h' == h
            then Right (portMap, subst)
            else Left "extendMatch: port mapping conflict"
        Nothing -> do
          subst' <- unifyPorts subst p h
          pure (M.insert p h portMap, subst')
    unifyPorts subst p h = do
      pTy <- requirePortType lhs p
      hTy <- requirePortType host h
      s1 <- unifyTy (applySubstTy subst pTy) hTy
      pure (composeSubst s1 subst)

requirePortType :: Diagram -> PortId -> Either Text TypeExpr
requirePortType diag pid =
  case diagramPortType diag pid of
    Nothing -> Left "match: missing port type"
    Just ty -> Right ty

pickNextEdge :: Match -> M.Map EdgeId (S.Set EdgeId) -> [EdgeId] -> Maybe EdgeId
pickNextEdge match adj allEdges =
  case M.keys (mEdges match) of
    [] -> safeHead allEdges
    mapped ->
      let mappedSet = S.fromList mapped
          adjacent = S.unions (map (\e -> M.findWithDefault S.empty e adj) mapped)
          candidates = filter (`S.notMember` mappedSet) (S.toList adjacent)
      in case candidates of
          [] -> safeHead (filter (`S.notMember` mappedSet) allEdges)
          _ -> safeHead (sortEdges candidates)

sortEdges :: [EdgeId] -> [EdgeId]
sortEdges = sortOn edgeKey
  where
    edgeKey (EdgeId k) = k

safeHead :: [a] -> Maybe a
safeHead [] = Nothing
safeHead (x:_) = Just x

adjacency :: Diagram -> M.Map EdgeId (S.Set EdgeId)
adjacency diag =
  let edgeList = IM.elems (dEdges diag)
      portsToEdges = foldl insertEdge M.empty edgeList
      insertEdge acc edge = foldl (insertPort edge) acc (eIns edge <> eOuts edge)
      insertPort edge acc pid = M.insertWith S.union pid (S.singleton (eId edge)) acc
      edgeAdj edge =
        let incident = S.unions [ M.findWithDefault S.empty pid portsToEdges | pid <- eIns edge <> eOuts edge ]
        in S.delete (eId edge) incident
  in M.fromList [ (eId e, edgeAdj e) | e <- edgeList ]

danglingOk :: Diagram -> Diagram -> Match -> Bool
danglingOk lhs host match =
  all okPort internalPorts
  where
    boundary = S.fromList (dIn lhs <> dOut lhs)
    allPorts = S.fromList (diagramPortIds lhs)
    internalPorts = S.toList (S.difference allPorts boundary)
    hostBoundary = S.fromList (dIn host <> dOut host)
    okPort p =
      case M.lookup p (mPorts match) of
        Nothing -> False
        Just pHost ->
          if pHost `S.member` hostBoundary
            then False
            else
          let prod = IM.lookup (portKey pHost) (dProd host)
              cons = IM.lookup (portKey pHost) (dCons host)
              matchedEdges = S.fromList (M.elems (mEdges match))
          in okEdge prod matchedEdges && okEdge cons matchedEdges
    okEdge entry matched =
      case entry of
        Just (Just eid) -> eid `S.member` matched
        Just Nothing -> True
        Nothing -> False
    portKey (PortId k) = k
