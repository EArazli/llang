{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Match
  ( Match(..)
  , findFirstMatch
  , findAllMatches
  , findFirstMatchNoDoc
  , findAllMatchesNoDoc
  , findFirstMatchWithTyVars
  , findAllMatchesWithTyVars
  ) where

import Data.Text (Text)
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import qualified Data.Set as S
import Data.List (sortOn)
import Strat.Poly.Graph
import Strat.Poly.Diagram (applySubstDiagram, applyAttrSubstDiagram, freeTyVarsDiagram, freeAttrVarsDiagram)
import Strat.Poly.Doctrine (Doctrine, dModes)
import Strat.Poly.TypeExpr (TypeExpr(..), TyVar)
import Strat.Poly.UnifyTy
import Strat.Poly.Attr
import Strat.Poly.ModeTheory (ModeTheory, emptyModeTheory)


data Match = Match
  { mPorts :: M.Map PortId PortId
  , mEdges :: M.Map EdgeId EdgeId
  , mTySub :: Subst
  , mAttrSub :: AttrSubst
  , mUsedHostPorts :: S.Set PortId
  , mUsedHostEdges :: S.Set EdgeId
  } deriving (Eq, Show)

findFirstMatch :: Doctrine -> Diagram -> Diagram -> Either Text (Maybe Match)
findFirstMatch doc lhs host =
  findFirstMatchInternal (dModes doc) (freeTyVarsDiagram lhs) (freeAttrVarsDiagram lhs) lhs host

findAllMatches :: Doctrine -> Diagram -> Diagram -> Either Text [Match]
findAllMatches doc lhs host =
  findAllMatchesInternal (dModes doc) (freeTyVarsDiagram lhs) (freeAttrVarsDiagram lhs) lhs host

findFirstMatchNoDoc :: Diagram -> Diagram -> Either Text (Maybe Match)
findFirstMatchNoDoc lhs host =
  findFirstMatchInternal emptyModeTheory (freeTyVarsDiagram lhs) (freeAttrVarsDiagram lhs) lhs host

findAllMatchesNoDoc :: Diagram -> Diagram -> Either Text [Match]
findAllMatchesNoDoc lhs host =
  findAllMatchesInternal emptyModeTheory (freeTyVarsDiagram lhs) (freeAttrVarsDiagram lhs) lhs host

findFirstMatchWithTyVars :: S.Set TyVar -> Diagram -> Diagram -> Either Text (Maybe Match)
findFirstMatchWithTyVars flex lhs host = do
  matches <- findAllMatchesInternal emptyModeTheory flex (freeAttrVarsDiagram lhs) lhs host
  pure (case matches of
          [] -> Nothing
          (m:_) -> Just m)

findAllMatchesWithTyVars :: S.Set TyVar -> Diagram -> Diagram -> Either Text [Match]
findAllMatchesWithTyVars flex lhs host =
  findAllMatchesInternal emptyModeTheory flex (freeAttrVarsDiagram lhs) lhs host

findFirstMatchInternal :: ModeTheory -> S.Set TyVar -> S.Set AttrVar -> Diagram -> Diagram -> Either Text (Maybe Match)
findFirstMatchInternal mt tyFlex attrFlex lhs host = do
  matches <- findAllMatchesInternal mt tyFlex attrFlex lhs host
  pure (case matches of
          [] -> Nothing
          (m:_) -> Just m)

findAllMatchesInternal :: ModeTheory -> S.Set TyVar -> S.Set AttrVar -> Diagram -> Diagram -> Either Text [Match]
findAllMatchesInternal mt tyFlex attrFlex lhs host = do
  let lhsEdges = IM.elems (dEdges lhs)
  let hostEdges = IM.elems (dEdges host)
  let adj = adjacency lhs
  let allEdgeIds = map eId lhsEdges
  go [] (Match M.empty M.empty M.empty M.empty S.empty S.empty) adj allEdgeIds lhsEdges hostEdges
  where
    go acc match adj allEdgeIds lhsEdges hostEdges =
      case pickNextEdge match adj allEdgeIds of
        Nothing -> do
          case completeBoundary mt tyFlex lhs host match of
            Left _ -> Right acc
            Right match' ->
              if danglingOk lhs host match'
                then Right (acc <> [match'])
                else Right acc
        Just eid -> do
          edge <- lookupEdge lhs eid
          let candidates = filter (edgeCompatible match edge) hostEdges
          tryCandidates acc match adj allEdgeIds edge candidates
    tryCandidates acc match adj allEdgeIds edge [] = Right acc
    tryCandidates acc match adj allEdgeIds edge (cand:cands) = do
      case extendMatch mt tyFlex attrFlex lhs host match edge cand of
        Left _ -> tryCandidates acc match adj allEdgeIds edge cands
        Right matches -> do
          acc' <- foldl step (Right acc) matches
          tryCandidates acc' match adj allEdgeIds edge cands
      where
        step acc0 m = do
          acc1 <- acc0
          go acc1 m adj allEdgeIds (IM.elems (dEdges lhs)) (IM.elems (dEdges host))

lookupEdge :: Diagram -> EdgeId -> Either Text Edge
lookupEdge diag eid =
  case IM.lookup (edgeKey eid) (dEdges diag) of
    Nothing -> Left "match: missing edge id"
    Just e -> Right e
  where
    edgeKey (EdgeId k) = k

edgeCompatible :: Match -> Edge -> Edge -> Bool
edgeCompatible match pat host =
  payloadCompatible (ePayload pat) (ePayload host)
    && length (eIns pat) == length (eIns host)
    && length (eOuts pat) == length (eOuts host)
    && portsCompatible match (eIns pat) (eIns host)
    && portsCompatible match (eOuts pat) (eOuts host)

payloadCompatible :: EdgePayload -> EdgePayload -> Bool
payloadCompatible p h =
  case (p, h) of
    (PGen g1 attrs1, PGen g2 attrs2) ->
      g1 == g2 && M.keysSet attrs1 == M.keysSet attrs2
    (PBox _ _, PBox _ _) -> True
    _ -> False

portsCompatible :: Match -> [PortId] -> [PortId] -> Bool
portsCompatible match pats hosts =
  and (zipWith ok pats hosts)
  where
    ok p h =
      case M.lookup p (mPorts match) of
        Nothing -> h `S.notMember` mUsedHostPorts match
        Just h' -> h' == h

extendMatch :: ModeTheory -> S.Set TyVar -> S.Set AttrVar -> Diagram -> Diagram -> Match -> Edge -> Edge -> Either Text [Match]
extendMatch mt tyFlex attrFlex lhs host match patEdge hostEdge = do
  if M.member (eId patEdge) (mEdges match)
    then Right []
    else if eId hostEdge `S.member` mUsedHostEdges match
      then Right []
      else do
        let pairs = zip (eIns patEdge <> eOuts patEdge) (eIns hostEdge <> eOuts hostEdge)
        substs <- payloadSubsts mt tyFlex attrFlex lhs host match patEdge hostEdge
        fmap concat (mapM (extendWithSubst pairs) substs)
  where
    extendWithSubst pairs (tySubst0, attrSubst0) =
      case foldl step (Right (mPorts match, mUsedHostPorts match, tySubst0, attrSubst0)) pairs of
        Left _ -> Right []
        Right (portMap, usedPorts, tySubst, attrSubst) ->
          let edgeMap = M.insert (eId patEdge) (eId hostEdge) (mEdges match)
              usedEdges = S.insert (eId hostEdge) (mUsedHostEdges match)
          in Right
            [ match
                { mPorts = portMap
                , mEdges = edgeMap
                , mTySub = tySubst
                , mAttrSub = attrSubst
                , mUsedHostPorts = usedPorts
                , mUsedHostEdges = usedEdges
                }
            ]
      where
        step acc (p, h) = do
          (portMap, usedPorts, tySubst, attrSubst) <- acc
          case M.lookup p portMap of
            Just h' ->
              if h' == h
                then Right (portMap, usedPorts, tySubst, attrSubst)
                else Left "extendMatch: port mapping conflict"
            Nothing ->
              if h `S.member` usedPorts
                then Left "extendMatch: host port already used"
                else do
                  tySubst' <- unifyPorts tySubst p h
                  pure (M.insert p h portMap, S.insert h usedPorts, tySubst', attrSubst)
    unifyPorts tySubst p h = do
      pTy <- requirePortType lhs p
      hTy <- requirePortType host h
      s1 <- unifyTyFlex mt tyFlex (applySubstTy mt tySubst pTy) hTy
      pure (composeSubst mt s1 tySubst)

payloadSubsts :: ModeTheory -> S.Set TyVar -> S.Set AttrVar -> Diagram -> Diagram -> Match -> Edge -> Edge -> Either Text [(Subst, AttrSubst)]
payloadSubsts mt tyFlex attrFlex _ _ match patEdge hostEdge =
  case (ePayload patEdge, ePayload hostEdge) of
    (PGen g1 attrs1, PGen g2 attrs2) ->
      if g1 /= g2 || M.keysSet attrs1 /= M.keysSet attrs2
        then Right []
        else do
          attrSubst <- foldl unifyField (Right (mAttrSub match)) (M.toList attrs1)
          Right [(mTySub match, attrSubst)]
      where
        unifyField acc (field, term1) = do
          sub <- acc
          case M.lookup field attrs2 of
            Nothing -> Left "match: missing attribute field"
            Just term2 -> unifyAttrFlex attrFlex sub term1 term2
    (PBox _ d1, PBox _ d2) -> do
      let tySubst = mTySub match
      let attrSubst = mAttrSub match
      let d1' = applyAttrSubstDiagram attrSubst (applySubstDiagram mt tySubst d1)
      let d2' = applyAttrSubstDiagram attrSubst (applySubstDiagram mt tySubst d2)
      subs <- diagramIsoMatchWithVars mt tyFlex attrFlex d1' d2'
      Right
        [ (composeSubst mt tySub tySubst, composeAttrSubst attrSub attrSubst)
        | (tySub, attrSub) <- subs
        ]
    _ -> Right []

requirePortType :: Diagram -> PortId -> Either Text TypeExpr
requirePortType diag pid =
  case diagramPortType diag pid of
    Nothing -> Left "match: missing port type"
    Just ty -> Right ty

completeBoundary :: ModeTheory -> S.Set TyVar -> Diagram -> Diagram -> Match -> Either Text Match
completeBoundary mt flex lhs host match =
  foldl step (Right match) (dIn lhs <> dOut lhs)
  where
    step acc p = do
      m <- acc
      case M.lookup p (mPorts m) of
        Just _ -> Right m
        Nothing -> mapFreshPort m p
    mapFreshPort m p = do
      pTy <- requirePortType lhs p
      let candidates = diagramPortIds host
      chooseCandidate m p pTy candidates
    chooseCandidate _ _ _ [] = Left "match: could not map boundary port"
    chooseCandidate m p pTy (h:rest) =
      if h `S.member` mUsedHostPorts m
        then chooseCandidate m p pTy rest
        else case requirePortType host h of
          Left _ -> chooseCandidate m p pTy rest
          Right hTy ->
            case unifyTyFlex mt flex (applySubstTy mt (mTySub m) pTy) hTy of
              Left _ -> chooseCandidate m p pTy rest
              Right s1 ->
                let subst' = composeSubst mt s1 (mTySub m)
                    ports' = M.insert p h (mPorts m)
                    used' = S.insert h (mUsedHostPorts m)
                in Right m { mPorts = ports', mUsedHostPorts = used', mTySub = subst' }

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
