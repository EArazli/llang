{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.CriticalPairs
  ( CPMode(..)
  , CriticalPair(..)
  , CriticalPairInfo(..)
  , criticalPairsForDoctrine
  , criticalPairsForRules
  ) where

import Data.Text (Text)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.IntMap.Strict as IM
import qualified Data.List as L
import Strat.Poly.Graph
import Strat.Poly.Diagram
import Strat.Poly.Match (Match(..))
import Strat.Poly.TypeExpr (TyVar(..), TypeExpr(..))
import Strat.Poly.UnifyTy (Subst, applySubstTy, unifyTyFlex, composeSubst)
import Strat.Poly.Rewrite (RewriteRule(..))
import Strat.Poly.Doctrine (Doctrine(..))
import Strat.Poly.Cell2 (Cell2(..))
import Strat.Common.Rules (RewritePolicy(..))
import Strat.Common.Rules (RuleClass(..), Orientation(..))


data CPMode = CP_All | CP_OnlyStructural | CP_StructuralVsComputational
  deriving (Eq, Ord, Show)

data CriticalPair = CriticalPair
  { cpRule1   :: Text
  , cpRule2   :: Text
  , cpOverlap :: Diagram
  , cpLeft    :: Diagram
  , cpRight   :: Diagram
  } deriving (Eq, Show)

data CriticalPairInfo = CriticalPairInfo
  { cpiPair :: CriticalPair
  , cpiClass1 :: RuleClass
  , cpiClass2 :: RuleClass
  } deriving (Eq, Show)

data RuleInfo = RuleInfo
  { riLabel :: Text
  , riRule  :: RewriteRule
  , riClass :: RuleClass
  } deriving (Eq, Show)

data PartialIso = PartialIso
  { piEdgeMap :: M.Map EdgeId EdgeId
  , piPortMap :: M.Map PortId PortId
  , piUsedEdges :: S.Set EdgeId
  , piUsedPorts :: S.Set PortId
  , piSubst :: Subst
  } deriving (Eq, Show)

criticalPairsForDoctrine :: CPMode -> RewritePolicy -> Doctrine -> Either Text [CriticalPairInfo]
criticalPairsForDoctrine mode policy doc =
  criticalPairsForRules mode (rulesWithClass policy (dCells2 doc))

criticalPairsForRules :: CPMode -> [RuleInfo] -> Either Text [CriticalPairInfo]
criticalPairsForRules mode rules = do
  let indexed = zip [0 :: Int ..] rules
  let pairs =
        [ (r1, r2)
        | (i, r1) <- indexed
        , (j, r2) <- indexed
        , i <= j
        , allowedPairSym mode r1 r2
        ]
  pairsOut <- fmap concat (mapM (uncurry criticalPairsForPair) pairs)
  dedupCriticalPairs pairsOut
  where
    allowedPairSym m a b = allowedPair m a b || allowedPair m b a

allowedPair :: CPMode -> RuleInfo -> RuleInfo -> Bool
allowedPair mode r1 r2 =
  case mode of
    CP_All -> True
    CP_OnlyStructural -> riClass r1 == Structural && riClass r2 == Structural
    CP_StructuralVsComputational ->
      (riClass r1 == Structural && riClass r2 == Computational)
        || (riClass r1 == Computational && riClass r2 == Structural)

criticalPairsForPair :: RuleInfo -> RuleInfo -> Either Text [CriticalPairInfo]
criticalPairsForPair r1 r2 = do
  let r1' = renameRule ":0" (riRule r1)
  let r2' = renameRule ":1" (riRule r2)
  let flex = S.fromList (rrTyVars r1' <> rrTyVars r2')
  overlaps <- enumerateOverlaps flex (rrLHS r1') (rrLHS r2')
  fmap concat (mapM (buildPair r1 r2 r1' r2') overlaps)
  where
    buildPair r1Info r2Info rule1 rule2 ov = do
      (host, match1, match2) <- buildOverlapHost (rrLHS rule1) (rrLHS rule2) ov
      if danglingOk (rrLHS rule1) host match1 && danglingOk (rrLHS rule2) host match2
        then do
          left <- applyRuleAtMatch rule1 match1 host
          right <- applyRuleAtMatch rule2 match2 host
          overlap' <- renumberDiagram host
          left' <- renumberDiagram left
          right' <- renumberDiagram right
          let cp = CriticalPair
                { cpRule1 = riLabel r1Info
                , cpRule2 = riLabel r2Info
                , cpOverlap = overlap'
                , cpLeft = left'
                , cpRight = right'
                }
          pure [CriticalPairInfo cp (riClass r1Info) (riClass r2Info)]
        else Right []

rulesWithClass :: RewritePolicy -> [Cell2] -> [RuleInfo]
rulesWithClass policy = concatMap (rulesForCellWithClass policy)

rulesForCellWithClass :: RewritePolicy -> Cell2 -> [RuleInfo]
rulesForCellWithClass policy cell =
  case policy of
    UseStructuralAsBidirectional ->
      case c2Class cell of
        Structural -> both
        Computational -> oriented
    UseOnlyComputationalLR ->
      case c2Class cell of
        Computational ->
          case c2Orient cell of
            LR -> [mk "lr" (c2LHS cell) (c2RHS cell)]
            Bidirectional -> [mk "lr" (c2LHS cell) (c2RHS cell)]
            _ -> []
        Structural -> []
    UseAllOriented -> oriented
  where
    mk suffix lhs rhs =
      let label = c2Name cell <> "." <> suffix
          rule = RewriteRule
            { rrName = label
            , rrLHS = lhs
            , rrRHS = rhs
            , rrTyVars = c2TyVars cell
            }
      in RuleInfo label rule (c2Class cell)
    oriented =
      case c2Orient cell of
        LR -> [mk "lr" (c2LHS cell) (c2RHS cell)]
        RL -> [mk "rl" (c2RHS cell) (c2LHS cell)]
        Bidirectional -> [mk "lr" (c2LHS cell) (c2RHS cell), mk "rl" (c2RHS cell) (c2LHS cell)]
        Unoriented -> []
    both =
      [ mk "lr" (c2LHS cell) (c2RHS cell)
      , mk "rl" (c2RHS cell) (c2LHS cell)
      ]

renameRule :: Text -> RewriteRule -> RewriteRule
renameRule suffix rule =
  let ren = M.fromList [ (v, TVar (renameVar v)) | v <- rrTyVars rule ]
      renameVar v = v { tvName = tvName v <> suffix }
      lhs' = applySubstDiagram ren (rrLHS rule)
      rhs' = applySubstDiagram ren (rrRHS rule)
      tyvars' = map renameVar (rrTyVars rule)
  in rule { rrLHS = lhs', rrRHS = rhs', rrTyVars = tyvars' }

enumerateOverlaps :: S.Set TyVar -> Diagram -> Diagram -> Either Text [PartialIso]
enumerateOverlaps flex l1 l2 = do
  let edges1 = sortEdges (IM.elems (dEdges l1))
  let edges2 = sortEdges (IM.elems (dEdges l2))
  fmap concat (mapM (seedFrom edges2) edges1)
  where
    emptyState = PartialIso M.empty M.empty S.empty S.empty M.empty
    seedFrom edges2 e1 =
      fmap concat (mapM (expandFromSeed e1) edges2)
    expandFromSeed e1 e2 = do
      seeds <- mapEdge flex l1 l2 emptyState e1 e2
      fmap concat (mapM (expandState l1 l2 flex) seeds)

expandState :: Diagram -> Diagram -> S.Set TyVar -> PartialIso -> Either Text [PartialIso]
expandState l1 l2 flex st = do
  let mappedPorts = S.fromList (M.keys (piPortMap st))
  let candidates =
        [ e
        | e <- sortEdges (IM.elems (dEdges l1))
        , M.notMember (eId e) (piEdgeMap st)
        , any (`S.member` mappedPorts) (eIns e <> eOuts e)
        ]
  expanded <- fmap concat (mapM (expandEdge l1 l2 flex st) candidates)
  deeper <- fmap concat (mapM (expandState l1 l2 flex) expanded)
  pure (st : deeper)

expandEdge :: Diagram -> Diagram -> S.Set TyVar -> PartialIso -> Edge -> Either Text [PartialIso]
expandEdge l1 l2 flex st e1 = do
  let candidates =
        [ e2
        | e2 <- sortEdges (IM.elems (dEdges l2))
        , eId e2 `S.notMember` piUsedEdges st
        , edgeCompatible e1 e2
        ]
  fmap concat (mapM (mapEdge flex l1 l2 st e1) candidates)

mapEdge :: S.Set TyVar -> Diagram -> Diagram -> PartialIso -> Edge -> Edge -> Either Text [PartialIso]
mapEdge flex l1 l2 st e1 e2 =
  if M.member (eId e1) (piEdgeMap st)
    then Right []
    else if eId e2 `S.member` piUsedEdges st
    then Right []
    else if length (eIns e1) /= length (eIns e2) || length (eOuts e1) /= length (eOuts e2)
      then Right []
      else do
        substs <- payloadSubsts flex (piSubst st) (ePayload e1) (ePayload e2)
        fmap concat (mapM extendPorts substs)
  where
    extendPorts subst0 = do
      let pairs = zip (eIns e1) (eIns e2) <> zip (eOuts e1) (eOuts e2)
      case foldl (extendPort l1 l2 flex) (Right (piPortMap st, piUsedPorts st, subst0)) pairs of
        Left _ -> Right []
        Right (portMap', usedPorts', subst') -> do
          let edgeMap' = M.insert (eId e1) (eId e2) (piEdgeMap st)
          let usedEdges' = S.insert (eId e2) (piUsedEdges st)
          pure [st { piEdgeMap = edgeMap', piPortMap = portMap', piUsedEdges = usedEdges', piUsedPorts = usedPorts', piSubst = subst' }]

extendPort :: Diagram -> Diagram -> S.Set TyVar -> Either Text (M.Map PortId PortId, S.Set PortId, Subst) -> (PortId, PortId) -> Either Text (M.Map PortId PortId, S.Set PortId, Subst)
extendPort l1 l2 flex acc (p1, p2) = do
  (portMap, usedPorts, subst) <- acc
  case M.lookup p1 portMap of
    Just p2' ->
      if p2' == p2 then Right (portMap, usedPorts, subst) else Left "criticalPairs: port mapping conflict"
    Nothing ->
      if p2 `S.member` usedPorts
        then Left "criticalPairs: target port already used"
        else do
          s1 <- unifyPorts l1 l2 flex subst p1 p2
          let subst' = composeSubst s1 subst
          Right (M.insert p1 p2 portMap, S.insert p2 usedPorts, subst')

unifyPorts :: Diagram -> Diagram -> S.Set TyVar -> Subst -> PortId -> PortId -> Either Text Subst
unifyPorts l1 l2 flex subst p1 p2 = do
  pTy <- requirePortType l1 p1
  hTy <- requirePortType l2 p2
  unifyTyFlex flex (applySubstTy subst pTy) (applySubstTy subst hTy)

payloadSubsts :: S.Set TyVar -> Subst -> EdgePayload -> EdgePayload -> Either Text [Subst]
payloadSubsts flex subst p1 p2 =
  case (p1, p2) of
    (PGen g1, PGen g2) ->
      if g1 == g2 then Right [subst] else Right []
    (PBox _ d1, PBox _ d2) -> do
      let d1' = applySubstDiagram subst d1
      let d2' = applySubstDiagram subst d2
      subs <- diagramIsoMatchWithTyVars flex d1' d2'
      Right (map (`composeSubst` subst) subs)
    _ -> Right []

edgeCompatible :: Edge -> Edge -> Bool
edgeCompatible e1 e2 =
  length (eIns e1) == length (eIns e2)
    && length (eOuts e1) == length (eOuts e2)
    && payloadCompatible (ePayload e1) (ePayload e2)

payloadCompatible :: EdgePayload -> EdgePayload -> Bool
payloadCompatible p1 p2 =
  case (p1, p2) of
    (PGen g1, PGen g2) -> g1 == g2
    (PBox _ _, PBox _ _) -> True
    _ -> False

sortEdges :: [Edge] -> [Edge]
sortEdges = L.sortOn (\e -> edgeKey (eId e))
  where
    edgeKey (EdgeId k) = k

requirePortType :: Diagram -> PortId -> Either Text TypeExpr
requirePortType diag pid =
  case diagramPortType diag pid of
    Nothing -> Left "criticalPairs: missing port type"
    Just ty -> Right ty

buildOverlapHost :: Diagram -> Diagram -> PartialIso -> Either Text (Diagram, Match, Match)
buildOverlapHost l1 l2 ov = do
  let subst = piSubst ov
  let l1' = applySubstDiagram subst l1
  let l2' = applySubstDiagram subst l2
  let portMapL2 = M.fromList [ (p2, p1) | (p1, p2) <- M.toList (piPortMap ov) ]
  let edgeMapL2 = M.fromList [ (e2, e1) | (e1, e2) <- M.toList (piEdgeMap ov) ]
  (host1, portMap1, edgeMap1) <- insertEdgesFromL2 l1' l2' portMapL2 edgeMapL2
  (host2, portMap2) <- mapBoundaryPorts host1 l2' portMap1
  let host3 =
        host2
          { dIn = dedupePorts (dIn l1' <> mapPorts portMap2 (dIn l2'))
          , dOut = dedupePorts (dOut l1' <> mapPorts portMap2 (dOut l2'))
          }
  validateDiagram host3
  let m1 = mkIdentityMatch subst l1'
  let m2 = mkMatchForL2 subst l2' portMap2 edgeMap1
  pure (host3, m1, m2)

insertEdgesFromL2 :: Diagram -> Diagram -> M.Map PortId PortId -> M.Map EdgeId EdgeId -> Either Text (Diagram, M.Map PortId PortId, M.Map EdgeId EdgeId)
insertEdgesFromL2 host l2 portMap edgeMap =
  foldl step (Right (host, portMap, edgeMap)) (sortEdges (IM.elems (dEdges l2)))
  where
    step acc edge =
      case acc of
        Left err -> Left err
        Right (h, pm, em) ->
          case M.lookup (eId edge) em of
            Just _ -> Right (h, pm, em)
            Nothing -> do
              (h1, pm1, insHost) <- mapPortsInto h l2 pm (eIns edge)
              (h2, pm2, outsHost) <- mapPortsInto h1 l2 pm1 (eOuts edge)
              let newEdgeId = EdgeId (dNextEdge h2)
              h3 <- addEdgePayload (ePayload edge) insHost outsHost h2
              let em' = M.insert (eId edge) newEdgeId em
              Right (h3, pm2, em')

mapPortsInto :: Diagram -> Diagram -> M.Map PortId PortId -> [PortId] -> Either Text (Diagram, M.Map PortId PortId, [PortId])
mapPortsInto host l2 portMap ports =
  foldl step (Right (host, portMap, [])) ports
  where
    step acc p =
      case acc of
        Left err -> Left err
        Right (h, pm, accPorts) ->
          case M.lookup p pm of
            Just hp -> Right (h, pm, accPorts <> [hp])
            Nothing -> do
              ty <- requirePortType l2 p
              let (hp, h') = freshPort ty h
              Right (h', M.insert p hp pm, accPorts <> [hp])

mapBoundaryPorts :: Diagram -> Diagram -> M.Map PortId PortId -> Either Text (Diagram, M.Map PortId PortId)
mapBoundaryPorts host l2 portMap =
  foldl step (Right (host, portMap)) (dIn l2 <> dOut l2)
  where
    step acc p =
      case acc of
        Left err -> Left err
        Right (h, pm) ->
          case M.lookup p pm of
            Just _ -> Right (h, pm)
            Nothing -> do
              ty <- requirePortType l2 p
              let (hp, h') = freshPort ty h
              Right (h', M.insert p hp pm)

mapPorts :: M.Map PortId PortId -> [PortId] -> [PortId]
mapPorts mp = map (\p -> M.findWithDefault p p mp)

dedupePorts :: [PortId] -> [PortId]
dedupePorts = go S.empty
  where
    go _ [] = []
    go seen (p:ps)
      | p `S.member` seen = go seen ps
      | otherwise = p : go (S.insert p seen) ps

mkIdentityMatch :: Subst -> Diagram -> Match
mkIdentityMatch subst diag =
  let ports = diagramPortIds diag
      edges = IM.elems (dEdges diag)
      mPorts = M.fromList [ (p, p) | p <- ports ]
      mEdges = M.fromList [ (eId e, eId e) | e <- edges ]
      usedPorts = S.fromList ports
      usedEdges = S.fromList (map eId edges)
  in Match mPorts mEdges subst usedPorts usedEdges

mkMatchForL2 :: Subst -> Diagram -> M.Map PortId PortId -> M.Map EdgeId EdgeId -> Match
mkMatchForL2 subst l2 portMap edgeMap =
  let ports = diagramPortIds l2
      edges = IM.elems (dEdges l2)
      mPorts = M.fromList [ (p, M.findWithDefault p p portMap) | p <- ports ]
      mEdges = M.fromList [ (eId e, M.findWithDefault (eId e) (eId e) edgeMap) | e <- edges ]
      usedPorts = S.fromList (M.elems mPorts)
      usedEdges = S.fromList (M.elems mEdges)
  in Match mPorts mEdges subst usedPorts usedEdges

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

applyRuleAtMatch :: RewriteRule -> Match -> Diagram -> Either Text Diagram
applyRuleAtMatch rule match host = do
  let lhs = rrLHS rule
  let rhs = applySubstDiagram (mTySub match) (rrRHS rule)
  host1 <- deleteMatchedEdges host (M.elems (mEdges match))
  host2 <- deleteMatchedPorts host1 (internalPorts lhs) (mPorts match)
  let rhsShift = shiftDiagram (dNextPort host2) (dNextEdge host2) rhs
  host3 <- insertDiagram host2 rhsShift
  let lhsBoundary = dIn lhs <> dOut lhs
  let rhsBoundary = dIn rhsShift <> dOut rhsShift
  if length lhsBoundary /= length rhsBoundary
    then Left "criticalPairs: boundary length mismatch"
    else do
      (host4, _) <- foldl step (Right (host3, M.empty)) (zip lhsBoundary rhsBoundary)
      validateDiagram host4
      pure host4
  where
    step acc (lhsPort, rhsPort) = do
      (diag, seen) <- acc
      hostPort <- case M.lookup lhsPort (mPorts match) of
        Nothing -> Left "criticalPairs: missing boundary port mapping"
        Just p -> Right p
      case M.lookup rhsPort seen of
        Nothing -> do
          diag' <- mergePorts diag hostPort rhsPort
          pure (diag', M.insert rhsPort hostPort seen)
        Just hostPort' -> do
          diag' <- mergePorts diag hostPort' hostPort
          pure (diag', seen)

internalPorts :: Diagram -> [PortId]
internalPorts diag =
  let allPorts = S.fromList (diagramPortIds diag)
      boundary = S.fromList (dIn diag <> dOut diag)
  in S.toList (S.difference allPorts boundary)

deleteMatchedEdges :: Diagram -> [EdgeId] -> Either Text Diagram
deleteMatchedEdges diag edgeIds = foldl step (Right diag) edgeIds
  where
    step acc eid = do
      d <- acc
      case IM.lookup (edgeKey eid) (dEdges d) of
        Nothing -> Left "criticalPairs: missing edge"
        Just edge -> do
          let d1 = d { dEdges = IM.delete (edgeKey eid) (dEdges d) }
          let d2 = clearConsumers d1 (eIns edge)
          let d3 = clearProducers d2 (eOuts edge)
          pure d3
    edgeKey (EdgeId k) = k
    clearConsumers d ports =
      let clearOne mp p = IM.adjust (const Nothing) (portKey p) mp
          portKey (PortId k) = k
          mp = dCons d
      in d { dCons = foldl clearOne mp ports }
    clearProducers d ports =
      let clearOne mp p = IM.adjust (const Nothing) (portKey p) mp
          portKey (PortId k) = k
          mp = dProd d
      in d { dProd = foldl clearOne mp ports }

deleteMatchedPorts :: Diagram -> [PortId] -> M.Map PortId PortId -> Either Text Diagram
deleteMatchedPorts diag ports portMap = foldl step (Right diag) ports
  where
    step acc p = do
      d <- acc
      case M.lookup p portMap of
        Nothing -> Left "criticalPairs: missing port mapping"
        Just hostPort -> deletePort d hostPort

deletePort :: Diagram -> PortId -> Either Text Diagram
deletePort diag pid =
  let k = portKey pid
      portKey (PortId n) = n
  in case (IM.lookup k (dProd diag), IM.lookup k (dCons diag)) of
      (Just Nothing, Just Nothing) ->
        let d1 = diag
              { dPortTy = IM.delete k (dPortTy diag)
              , dProd = IM.delete k (dProd diag)
              , dCons = IM.delete k (dCons diag)
              , dIn = filter (/= pid) (dIn diag)
              , dOut = filter (/= pid) (dOut diag)
              }
        in Right d1
      _ -> Left "criticalPairs: cannot delete port with remaining incidence"

insertDiagram :: Diagram -> Diagram -> Either Text Diagram
insertDiagram base extra = do
  portTy <- unionDisjointIntMap "criticalPairs: insert ports" (dPortTy base) (dPortTy extra)
  prod <- unionDisjointIntMap "criticalPairs: insert producers" (dProd base) (dProd extra)
  cons <- unionDisjointIntMap "criticalPairs: insert consumers" (dCons base) (dCons extra)
  edges <- unionDisjointIntMap "criticalPairs: insert edges" (dEdges base) (dEdges extra)
  pure base
    { dPortTy = portTy
    , dProd = prod
    , dCons = cons
    , dEdges = edges
    , dNextPort = dNextPort extra
    , dNextEdge = dNextEdge extra
    }

dedupCriticalPairs :: [CriticalPairInfo] -> Either Text [CriticalPairInfo]
dedupCriticalPairs pairs = go [] pairs
  where
    go acc [] = Right acc
    go acc (p:ps) = do
      dup <- anyIso p acc
      if dup
        then go acc ps
        else go (acc <> [p]) ps

    anyIso _ [] = Right False
    anyIso p (x:xs) = do
      ok <- isoTriple (cpiPair p) (cpiPair x)
      if ok then Right True else anyIso p xs

    isoTriple a b = do
      okOverlap <- isoEqOrFalse (cpOverlap a) (cpOverlap b)
      if not okOverlap
        then Right False
        else do
          okDirect <- do
            okLeft <- isoEqOrFalse (cpLeft a) (cpLeft b)
            if okLeft then isoEqOrFalse (cpRight a) (cpRight b) else Right False
          if okDirect
            then Right True
            else do
              okSwap <- isoEqOrFalse (cpLeft a) (cpRight b)
              if okSwap then isoEqOrFalse (cpRight a) (cpLeft b) else Right False

    isoEqOrFalse x y =
      case diagramIsoEq x y of
        Left _ -> Right False
        Right ok -> Right ok
