{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Match
  ( Match(..)
  , findFirstMatch
  , findAllMatches
  , findFirstMatchNoDoc
  , findAllMatchesNoDoc
  , findFirstMatchWithTyVars
  , findAllMatchesWithTyVars
  , findFirstMatchWithTyVarsNoDoc
  , findAllMatchesWithTyVarsNoDoc
  , findFirstMatchWithVars
  , findAllMatchesWithVars
  ) where

import Data.Text (Text)
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import qualified Data.Set as S
import Data.List (sortOn)
import Strat.Poly.Graph
import Strat.Poly.Diagram
  ( applySubstDiagramTT
  , applyAttrSubstDiagram
  , freeTyVarsDiagram
  , freeIxVarsDiagram
  , freeAttrVarsDiagram
  )
import Strat.Poly.Doctrine (Doctrine, doctrineTypeTheory)
import Strat.Poly.TypeExpr (TypeExpr, TyVar, IxVar)
import Strat.Poly.UnifyTy
import Strat.Poly.Attr
import Strat.Poly.ModeTheory (ModeTheory, emptyModeTheory)
import Strat.Poly.TypeTheory (TypeTheory(..))


data Match = Match
  { mPortMap :: M.Map PortId PortId
  , mEdgeMap :: M.Map EdgeId EdgeId
  , mTySubst :: Subst
  , mAttrSubst :: AttrSubst
  , mBinderSub :: M.Map BinderMetaVar Diagram
  , mUsedHostPorts :: S.Set PortId
  , mUsedHostEdges :: S.Set EdgeId
  } deriving (Eq, Show)

mkLegacyTypeTheory :: ModeTheory -> TypeTheory
mkLegacyTypeTheory mt = TypeTheory { ttModes = mt, ttIndex = M.empty, ttTypeParams = M.empty, ttIxFuel = 200 }

applySubstTyCompat :: TypeTheory -> Subst -> TypeExpr -> TypeExpr
applySubstTyCompat tt subst ty =
  case applySubstTy tt subst ty of
    Right ty' -> ty'
    Left _ -> ty

composeSubstCompat :: TypeTheory -> Subst -> Subst -> Subst
composeSubstCompat tt s2 s1 =
  case composeSubst tt s2 s1 of
    Right s -> s
    Left _ -> s1

findFirstMatch :: Doctrine -> Diagram -> Diagram -> Either Text (Maybe Match)
findFirstMatch doc lhs host =
  findFirstMatchInternal
    (doctrineTypeTheory doc)
    (freeTyVarsDiagram lhs)
    (freeIxVarsDiagram lhs)
    (freeAttrVarsDiagram lhs)
    lhs
    host

findAllMatches :: Doctrine -> Diagram -> Diagram -> Either Text [Match]
findAllMatches doc lhs host =
  findAllMatchesInternal
    (doctrineTypeTheory doc)
    (freeTyVarsDiagram lhs)
    (freeIxVarsDiagram lhs)
    (freeAttrVarsDiagram lhs)
    lhs
    host

findFirstMatchNoDoc :: Diagram -> Diagram -> Either Text (Maybe Match)
findFirstMatchNoDoc lhs host =
  findFirstMatchInternal
    (mkLegacyTypeTheory emptyModeTheory)
    (freeTyVarsDiagram lhs)
    (freeIxVarsDiagram lhs)
    (freeAttrVarsDiagram lhs)
    lhs
    host

findAllMatchesNoDoc :: Diagram -> Diagram -> Either Text [Match]
findAllMatchesNoDoc lhs host =
  findAllMatchesInternal
    (mkLegacyTypeTheory emptyModeTheory)
    (freeTyVarsDiagram lhs)
    (freeIxVarsDiagram lhs)
    (freeAttrVarsDiagram lhs)
    lhs
    host

findFirstMatchWithTyVars :: ModeTheory -> S.Set TyVar -> Diagram -> Diagram -> Either Text (Maybe Match)
findFirstMatchWithTyVars mt flex lhs host = do
  matches <-
    findAllMatchesInternal
      (mkLegacyTypeTheory mt)
      flex
      S.empty
      (freeAttrVarsDiagram lhs)
      lhs
      host
  pure (case matches of [] -> Nothing; (m:_) -> Just m)

findAllMatchesWithTyVars :: ModeTheory -> S.Set TyVar -> Diagram -> Diagram -> Either Text [Match]
findAllMatchesWithTyVars mt flex lhs host =
  findAllMatchesInternal
    (mkLegacyTypeTheory mt)
    flex
    S.empty
    (freeAttrVarsDiagram lhs)
    lhs
    host

findFirstMatchWithTyVarsNoDoc :: S.Set TyVar -> Diagram -> Diagram -> Either Text (Maybe Match)
findFirstMatchWithTyVarsNoDoc = findFirstMatchWithTyVars emptyModeTheory

findAllMatchesWithTyVarsNoDoc :: S.Set TyVar -> Diagram -> Diagram -> Either Text [Match]
findAllMatchesWithTyVarsNoDoc = findAllMatchesWithTyVars emptyModeTheory

findFirstMatchWithVars
  :: TypeTheory
  -> S.Set TyVar
  -> S.Set IxVar
  -> Diagram
  -> Diagram
  -> Either Text (Maybe Match)
findFirstMatchWithVars tt tyFlex ixFlex lhs host =
  findFirstMatchInternal tt tyFlex ixFlex (freeAttrVarsDiagram lhs) lhs host

findAllMatchesWithVars
  :: TypeTheory
  -> S.Set TyVar
  -> S.Set IxVar
  -> Diagram
  -> Diagram
  -> Either Text [Match]
findAllMatchesWithVars tt tyFlex ixFlex lhs host =
  findAllMatchesInternal tt tyFlex ixFlex (freeAttrVarsDiagram lhs) lhs host

findFirstMatchInternal
  :: TypeTheory
  -> S.Set TyVar
  -> S.Set IxVar
  -> S.Set AttrVar
  -> Diagram
  -> Diagram
  -> Either Text (Maybe Match)
findFirstMatchInternal tt tyFlex ixFlex attrFlex lhs host = do
  matches <- findAllMatchesInternal tt tyFlex ixFlex attrFlex lhs host
  pure (case matches of [] -> Nothing; (m:_) -> Just m)

findAllMatchesInternal
  :: TypeTheory
  -> S.Set TyVar
  -> S.Set IxVar
  -> S.Set AttrVar
  -> Diagram
  -> Diagram
  -> Either Text [Match]
findAllMatchesInternal tt tyFlex ixFlex attrFlex lhs host = do
  let lhsEdges = IM.elems (dEdges lhs)
  let hostEdges = IM.elems (dEdges host)
  let adj = adjacency lhs
  let allEdgeIds = map eId lhsEdges
  go [] (Match M.empty M.empty emptySubst M.empty M.empty S.empty S.empty) adj allEdgeIds lhsEdges hostEdges
  where
    go acc match adj allEdgeIds lhsEdges hostEdges =
      case pickNextEdge match adj allEdgeIds of
        Nothing -> do
          case completeBoundary tt tyFlex ixFlex lhs host match of
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
      case extendMatch tt tyFlex ixFlex attrFlex lhs host match edge cand of
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
    (PGen g1 attrs1 bargs1, PGen g2 attrs2 bargs2) ->
      g1 == g2 && M.keysSet attrs1 == M.keysSet attrs2 && length bargs1 == length bargs2
    (PBox _ _, PBox _ _) -> True
    (PSplice x, PSplice y) -> x == y
    _ -> False

portsCompatible :: Match -> [PortId] -> [PortId] -> Bool
portsCompatible match pats hosts =
  and (zipWith ok pats hosts)
  where
    ok p h =
      case M.lookup p (mPortMap match) of
        Nothing -> h `S.notMember` mUsedHostPorts match
        Just h' -> h' == h

extendMatch
  :: TypeTheory
  -> S.Set TyVar
  -> S.Set IxVar
  -> S.Set AttrVar
  -> Diagram
  -> Diagram
  -> Match
  -> Edge
  -> Edge
  -> Either Text [Match]
extendMatch tt tyFlex ixFlex attrFlex lhs host match patEdge hostEdge = do
  if M.member (eId patEdge) (mEdgeMap match)
    then Right []
    else if eId hostEdge `S.member` mUsedHostEdges match
      then Right []
      else do
        let pairs = zip (eIns patEdge <> eOuts patEdge) (eIns hostEdge <> eOuts hostEdge)
        substs <- payloadSubsts tt tyFlex ixFlex attrFlex lhs host match patEdge hostEdge
        fmap concat (mapM (extendWithSubst pairs) substs)
  where
    extendWithSubst pairs (tySubst0, attrSubst0, binderSub0) =
      case foldl step (Right (mPortMap match, mUsedHostPorts match, tySubst0, attrSubst0)) pairs of
        Left _ -> Right []
        Right (portMap, usedPorts, tySubst, attrSubst) ->
          let edgeMap = M.insert (eId patEdge) (eId hostEdge) (mEdgeMap match)
              usedEdges = S.insert (eId hostEdge) (mUsedHostEdges match)
           in Right
                [ match
                    { mPortMap = portMap
                    , mEdgeMap = edgeMap
                    , mTySubst = tySubst
                    , mAttrSubst = attrSubst
                    , mBinderSub = binderSub0
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
      s1 <-
        unifyTyFlex
          tt
          (dIxCtx lhs)
          tyFlex
          ixFlex
          emptySubst
          (applySubstTyCompat tt tySubst pTy)
          hTy
      pure (composeSubstCompat tt s1 tySubst)

payloadSubsts
  :: TypeTheory
  -> S.Set TyVar
  -> S.Set IxVar
  -> S.Set AttrVar
  -> Diagram
  -> Diagram
  -> Match
  -> Edge
  -> Edge
  -> Either Text [(Subst, AttrSubst, M.Map BinderMetaVar Diagram)]
payloadSubsts tt tyFlex ixFlex attrFlex _ _ match patEdge hostEdge =
  case (ePayload patEdge, ePayload hostEdge) of
    (PGen g1 attrs1 bargs1, PGen g2 attrs2 bargs2) ->
      if g1 /= g2 || M.keysSet attrs1 /= M.keysSet attrs2 || length bargs1 /= length bargs2
        then Right []
        else do
          attrSubst <- foldl unifyField (Right (mAttrSubst match)) (M.toList attrs1)
          foldBinderArgs [(mTySubst match, attrSubst, mBinderSub match)] (zip bargs1 bargs2)
      where
        unifyField acc (field, term1) = do
          sub <- acc
          case M.lookup field attrs2 of
            Nothing -> Left "match: missing attribute field"
            Just term2 -> unifyAttrFlex attrFlex sub term1 term2

        foldBinderArgs acc [] = Right acc
        foldBinderArgs acc (pair:rest) = do
          expanded <- fmap concat (mapM (expandOne pair) acc)
          foldBinderArgs expanded rest

        expandOne (patArg, hostArg) (tySubst0, attrSubst0, binderSub0) =
          case (patArg, hostArg) of
            (BAConcrete dPat, BAConcrete dHost) ->
              case (applySubstDiagramTT tt tySubst0 dPat, applySubstDiagramTT tt tySubst0 dHost) of
                (Right dPatSub, Right dHostSub) -> do
                  let dPat' = applyAttrSubstDiagram attrSubst0 dPatSub
                  let dHost' = applyAttrSubstDiagram attrSubst0 dHostSub
                  subs <- diagramIsoMatchWithVars tt tyFlex ixFlex attrFlex dPat' dHost'
                  pure
                    [ (composeSubstCompat tt tySub tySubst0, composeAttrSubst attrSub attrSubst0, binderSub0)
                    | (tySub, attrSub) <- subs
                    ]
                _ -> Right []
            (BAMeta x, BAConcrete dHost) ->
              case M.lookup x binderSub0 of
                Nothing -> Right [(tySubst0, attrSubst0, M.insert x dHost binderSub0)]
                Just existing -> do
                  ok <- diagramIsoEq existing dHost
                  if ok
                    then Right [(tySubst0, attrSubst0, binderSub0)]
                    else Right []
            (BAMeta x, BAMeta y) ->
              if x == y
                then Right [(tySubst0, attrSubst0, binderSub0)]
                else Right []
            _ -> Right []

    (PBox _ d1, PBox _ d2) -> do
      let tySubst = mTySubst match
      let attrSubst = mAttrSubst match
      case (applySubstDiagramTT tt tySubst d1, applySubstDiagramTT tt tySubst d2) of
        (Right d1Sub, Right d2Sub) -> do
          let d1' = applyAttrSubstDiagram attrSubst d1Sub
          let d2' = applyAttrSubstDiagram attrSubst d2Sub
          subs <- diagramIsoMatchWithVars tt tyFlex ixFlex attrFlex d1' d2'
          Right
            [ (composeSubstCompat tt tySub tySubst, composeAttrSubst attrSub attrSubst, mBinderSub match)
            | (tySub, attrSub) <- subs
            ]
        _ -> Right []

    (PSplice x, PSplice y)
      | x == y -> Right [(mTySubst match, mAttrSubst match, mBinderSub match)]
      | otherwise -> Right []

    _ -> Right []

requirePortType :: Diagram -> PortId -> Either Text TypeExpr
requirePortType diag pid =
  case diagramPortType diag pid of
    Nothing -> Left "match: missing port type"
    Just ty -> Right ty

completeBoundary :: TypeTheory -> S.Set TyVar -> S.Set IxVar -> Diagram -> Diagram -> Match -> Either Text Match
completeBoundary tt flexTy flexIx lhs host match =
  foldl step (Right match) (dIn lhs <> dOut lhs)
  where
    step acc p = do
      m <- acc
      case M.lookup p (mPortMap m) of
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
            case
              unifyTyFlex
                tt
                (dIxCtx lhs)
                flexTy
                flexIx
                emptySubst
                (applySubstTyCompat tt (mTySubst m) pTy)
                hTy
              of
                Left _ -> chooseCandidate m p pTy rest
                Right s1 ->
                  let subst' = composeSubstCompat tt s1 (mTySubst m)
                      ports' = M.insert p h (mPortMap m)
                      used' = S.insert h (mUsedHostPorts m)
                   in Right m { mPortMap = ports', mUsedHostPorts = used', mTySubst = subst' }

pickNextEdge :: Match -> M.Map EdgeId (S.Set EdgeId) -> [EdgeId] -> Maybe EdgeId
pickNextEdge match adj allEdges =
  case M.keys (mEdgeMap match) of
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
        let incident = S.unions [M.findWithDefault S.empty pid portsToEdges | pid <- eIns edge <> eOuts edge]
         in S.delete (eId edge) incident
   in M.fromList [(eId e, edgeAdj e) | e <- edgeList]

danglingOk :: Diagram -> Diagram -> Match -> Bool
danglingOk lhs host match =
  all okPort internalPorts
  where
    boundary = S.fromList (dIn lhs <> dOut lhs)
    allPorts = S.fromList (diagramPortIds lhs)
    internalPorts = S.toList (S.difference allPorts boundary)
    hostBoundary = S.fromList (dIn host <> dOut host)

    okPort p =
      case M.lookup p (mPortMap match) of
        Nothing -> False
        Just pHost ->
          if pHost `S.member` hostBoundary
            then False
            else
              let prod = IM.lookup (portKey pHost) (dProd host)
                  cons = IM.lookup (portKey pHost) (dCons host)
                  matchedEdges = S.fromList (M.elems (mEdgeMap match))
               in okEdge prod matchedEdges && okEdge cons matchedEdges

    okEdge entry matched =
      case entry of
        Just (Just eid) -> eid `S.member` matched
        Just Nothing -> True
        Nothing -> False

    portKey (PortId k) = k
