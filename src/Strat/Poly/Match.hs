{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Match
  ( Match(..)
  , MatchConfig(..)
  , findFirstMatch
  , findAllMatches
  ) where

import Data.Text (Text)
import qualified Data.IntMap.Strict as IM
import qualified Data.List as L
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.Graph
import Strat.Poly.DiagramIso (diagramIsoEq, diagramIsoMatchWithVarsFrom)
import Strat.Poly.DiagramInterpretation (requirePortType)
import Strat.Poly.ModeTheory (ModeName)
import Strat.Poly.Names (GenName)
import Strat.Poly.Obj (TmVar, sameTmVarId)
import Strat.Poly.Syntax (CodeArg(..))
import Strat.Poly.Tele (GenParam)
import Strat.Poly.TypeTheory (TypeTheory, GenArgSig(..), lookupGenArgSig)
import Strat.Poly.UnifyObj
  ( Subst
  , applySubstCtx
  , emptySubst
  , unifyGenArgsFlex
  , unifyObjFlex
  )


data Match = Match
  { mPortMap :: M.Map PortId PortId
  , mEdgeMap :: M.Map EdgeId EdgeId
  , mTySubst :: Subst
  , mBinderSub :: M.Map BinderMetaVar Diagram
  , mUsedHostPorts :: S.Set PortId
  , mUsedHostEdges :: S.Set EdgeId
  }
  deriving (Eq, Show)

data MatchConfig = MatchConfig
  { mcTheory :: TypeTheory
  , mcFlex :: S.Set TmVar
  }
  deriving (Eq, Show)

findFirstMatch :: MatchConfig -> Diagram -> Diagram -> Either Text (Maybe Match)
findFirstMatch cfg lhs host = do
  matches <- findAllMatches cfg lhs host
  pure (safeHead matches)

findAllMatches :: MatchConfig -> Diagram -> Diagram -> Either Text [Match]
findAllMatches cfg lhs host
  | dMode lhs /= dMode host = Right []
  | otherwise = do
      lhsTmCtx <- applySubstCtx tt emptySubst (dTmCtx lhs)
      hostTmCtx <- applySubstCtx tt emptySubst (dTmCtx host)
      if lhsTmCtx /= hostTmCtx
        then Right []
        else do
          let lhsEdges = IM.elems (dEdges lhs)
              hostEdges = IM.elems (dEdges host)
              adj = adjacency lhs
              allEdgeIds = map eId lhsEdges
              emptyMatch = Match M.empty M.empty emptySubst M.empty S.empty S.empty
          go [] emptyMatch adj allEdgeIds lhsEdges hostEdges
  where
    tt = mcTheory cfg
    flex = mcFlex cfg

    go acc match adj allEdgeIds lhsEdges hostEdges =
      case pickNextEdge match adj allEdgeIds of
        Nothing ->
          case completeBoundary tt flex lhs host match of
            Left _ -> Right acc
            Right match'
              | danglingOk lhs host match' -> Right (acc <> [match'])
              | otherwise -> Right acc
        Just eid -> do
          edge <- lookupEdge lhs eid
          let candidates = filter (edgeCompatible match edge) hostEdges
          tryCandidates acc match adj allEdgeIds lhsEdges hostEdges edge candidates

    tryCandidates acc _ _ _ _ _ _ [] = Right acc
    tryCandidates acc match adj allEdgeIds lhsEdges hostEdges edge (cand : cands) =
      case extendMatch tt flex lhs host match edge cand of
        Left _ -> tryCandidates acc match adj allEdgeIds lhsEdges hostEdges edge cands
        Right matches -> do
          acc' <- foldl step (Right acc) matches
          tryCandidates acc' match adj allEdgeIds lhsEdges hostEdges edge cands
      where
        step acc0 m = do
          acc1 <- acc0
          go acc1 m adj allEdgeIds lhsEdges hostEdges

lookupEdge :: Diagram -> EdgeId -> Either Text Edge
lookupEdge diag eid =
  case IM.lookup (unEdgeId eid) (dEdges diag) of
    Nothing -> Left "match: missing edge id"
    Just e -> Right e

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
    (PGen g1 args1 bargs1, PGen g2 args2 bargs2) ->
      g1 == g2
        && length args1 == length args2
        && and (zipWith sameArgKind args1 args2)
        && length bargs1 == length bargs2
    (PBox _ _, PBox _ _) -> True
    (PFeedback _, PFeedback _) -> True
    (PSplice x me1, PSplice y me2) -> x == y && me1 == me2
    (PTmMeta x, PTmMeta y) -> sameTmVarId x y
    (PTmLit x, PTmLit y) -> x == y
    (PInternalDrop, PInternalDrop) -> True
    _ -> False
  where
    sameArgKind (CAObj _) (CAObj _) = True
    sameArgKind (CATm _) (CATm _) = True
    sameArgKind _ _ = False

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
  -> S.Set TmVar
  -> Diagram
  -> Diagram
  -> Match
  -> Edge
  -> Edge
  -> Either Text [Match]
extendMatch tt flex lhs host match patEdge hostEdge
  | M.member (eId patEdge) (mEdgeMap match) = Right []
  | eId hostEdge `S.member` mUsedHostEdges match = Right []
  | otherwise = do
      let pairs = zip (eIns patEdge <> eOuts patEdge) (eIns hostEdge <> eOuts hostEdge)
      substs <- payloadSubsts tt flex lhs match patEdge hostEdge
      fmap concat (mapM (extendWithSubst pairs) substs)
  where
    extendWithSubst pairs (tySubst0, binderSub0) =
      case foldl step (Right (mPortMap match, mUsedHostPorts match, tySubst0)) pairs of
        Left _ -> Right []
        Right (portMap, usedPorts, tySubst) ->
          let edgeMap = M.insert (eId patEdge) (eId hostEdge) (mEdgeMap match)
              usedEdges = S.insert (eId hostEdge) (mUsedHostEdges match)
           in Right
                [ match
                    { mPortMap = portMap
                    , mEdgeMap = edgeMap
                    , mTySubst = tySubst
                    , mBinderSub = binderSub0
                    , mUsedHostPorts = usedPorts
                    , mUsedHostEdges = usedEdges
                    }
                ]
      where
        step acc (p, h) = do
          (portMap, usedPorts, tySubst) <- acc
          case M.lookup p portMap of
            Just h'
              | h' == h -> Right (portMap, usedPorts, tySubst)
              | otherwise -> Left "extendMatch: port mapping conflict"
            Nothing
              | h `S.member` usedPorts -> Left "extendMatch: host port already used"
              | otherwise -> do
                  tySubst' <- unifyPorts tySubst p h
                  pure (M.insert p h portMap, S.insert h usedPorts, tySubst')

    unifyPorts tySubst p h = do
      pTy <- requirePortType "match" lhs p
      hTy <- requirePortType "match" host h
      unifyObjFlex
        tt
        (dTmCtx lhs)
        flex
        tySubst
        pTy
        hTy

payloadSubsts
  :: TypeTheory
  -> S.Set TmVar
  -> Diagram
  -> Match
  -> Edge
  -> Edge
  -> Either Text [(Subst, M.Map BinderMetaVar Diagram)]
payloadSubsts tt flex lhs match patEdge hostEdge =
  case (ePayload patEdge, ePayload hostEdge) of
    (PGen g1 args1 bargs1, PGen g2 args2 bargs2)
      | g1 /= g2
          || length args1 /= length args2
          || length bargs1 /= length bargs2 -> Right []
      | otherwise -> do
          tmCtx' <- applySubstCtx tt (mTySubst match) (dTmCtx lhs)
          case lookupGenArgParams tt (dMode lhs) g1 args1 args2 of
            Nothing -> Right []
            Just params -> do
              tySubst <- unifyGenArgsFlex tt tmCtx' flex (mTySubst match) params args1 args2
              foldBinderArgs [(tySubst, mBinderSub match)] (zip bargs1 bargs2)
      where
        foldBinderArgs acc [] = Right acc
        foldBinderArgs acc (pair : rest) = do
          expanded <- fmap concat (mapM (expandOne pair) acc)
          foldBinderArgs expanded rest

        expandOne (patArg, hostArg) (tySubst0, binderSub0) =
          case (patArg, hostArg) of
            (BAConcrete dPat, BAConcrete dHost) -> do
              subs <- diagramIsoMatchWithVarsFrom tt flex tySubst0 dPat dHost
              pure [ (tySub', binderSub0) | tySub' <- subs ]
            (BAMeta x, BAConcrete dHost) ->
              case M.lookup x binderSub0 of
                Nothing -> Right [(tySubst0, M.insert x dHost binderSub0)]
                Just existing -> do
                  ok <- diagramIsoEq existing dHost
                  if ok
                    then Right [(tySubst0, binderSub0)]
                    else Right []
            (BAMeta x, BAMeta y)
              | x == y -> Right [(tySubst0, binderSub0)]
              | otherwise -> Right []
            _ -> Right []

    (PBox _ d1, PBox _ d2) -> do
      subs <- diagramIsoMatchWithVarsFrom tt flex (mTySubst match) d1 d2
      pure [ (tySub', mBinderSub match) | tySub' <- subs ]

    (PFeedback d1, PFeedback d2) -> do
      subs <- diagramIsoMatchWithVarsFrom tt flex (mTySubst match) d1 d2
      pure [ (tySub', mBinderSub match) | tySub' <- subs ]

    (PSplice x me1, PSplice y me2)
      | x == y && me1 == me2 -> Right [(mTySubst match, mBinderSub match)]
      | otherwise -> Right []

    (PTmMeta x, PTmMeta y)
      | sameTmVarId x y -> Right [(mTySubst match, mBinderSub match)]
      | otherwise -> Right []

    (PTmLit x, PTmLit y)
      | x == y -> Right [(mTySubst match, mBinderSub match)]
      | otherwise -> Right []

    (PInternalDrop, PInternalDrop) ->
      Right [(mTySubst match, mBinderSub match)]

    _ -> Right []

lookupGenArgParams :: TypeTheory -> ModeName -> GenName -> [CodeArg] -> [CodeArg] -> Maybe [GenParam]
lookupGenArgParams tt mode g _args1 _args2 =
  case lookupGenArgSig tt mode g of
    Just sig -> Just (gasParams sig)
    Nothing -> Nothing

completeBoundary
  :: TypeTheory
  -> S.Set TmVar
  -> Diagram
  -> Diagram
  -> Match
  -> Either Text Match
completeBoundary tt flex lhs host match =
  foldl step (Right match) (dIn lhs <> dOut lhs)
  where
    step acc p = do
      m <- acc
      case M.lookup p (mPortMap m) of
        Just _ -> Right m
        Nothing -> mapFreshPort m p

    mapFreshPort m p = do
      pTy <- requirePortType "match" lhs p
      let candidates = diagramPortIds host
      chooseCandidate m p pTy candidates

    chooseCandidate _ _ _ [] = Left "match: could not map boundary port"
    chooseCandidate m p pTy (h : rest)
      | h `S.member` mUsedHostPorts m = chooseCandidate m p pTy rest
      | otherwise =
          case requirePortType "match" host h of
            Left _ -> chooseCandidate m p pTy rest
            Right hTy ->
              case
                unifyObjFlex
                  tt
                  (dTmCtx lhs)
                  flex
                  (mTySubst m)
                  pTy
                  hTy
                of
                Left _ -> chooseCandidate m p pTy rest
                Right subst' ->
                  let ports' = M.insert p h (mPortMap m)
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
sortEdges = L.sortOn unEdgeId

safeHead :: [a] -> Maybe a
safeHead [] = Nothing
safeHead (x : _) = Just x

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
              let prod = IM.lookup (unPortId pHost) (dProd host)
                  cons = IM.lookup (unPortId pHost) (dCons host)
                  matchedEdges = S.fromList (M.elems (mEdgeMap match))
               in okEdge prod matchedEdges && okEdge cons matchedEdges

    okEdge entry matched =
      case entry of
        Just (Just eid) -> eid `S.member` matched
        Just Nothing -> True
        Nothing -> False
