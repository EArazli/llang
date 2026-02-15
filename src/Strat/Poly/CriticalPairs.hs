{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.CriticalPairs
  ( CPMode(..)
  , CriticalPair(..)
  , CriticalPairInfo(..)
  , RuleInfo(..)
  , criticalPairsForDoctrine
  , criticalPairsForRules
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.IntMap.Strict as IM
import qualified Data.List as L
import Data.Functor.Identity (runIdentity)
import Strat.Poly.Graph
import qualified Strat.Poly.Diagram as Diag
import Strat.Poly.Diagram
import Strat.Poly.Match (Match(..))
import Strat.Poly.TypeExpr (TyVar(..), TmVar(..), TermDiagram(..), TypeExpr(..), mapTypeExpr)
import qualified Strat.Poly.UnifyTy as U
import Strat.Poly.Attr
import Strat.Poly.Rewrite (RewriteRule(..))
import Strat.Poly.Doctrine (Doctrine(..), doctrineTypeTheory)
import Strat.Poly.Cell2 (Cell2(..))
import Strat.Common.Rules (RewritePolicy(..))
import Strat.Common.Rules (RuleClass(..), Orientation(..))
import Strat.Poly.ModeTheory (ModeTheory)
import Strat.Poly.TypeTheory (TypeTheory, modeOnlyTypeTheory)
import Strat.Poly.Traversal (traverseDiagram)


type Subst = U.Subst

fatalSubstPrefix :: Text
fatalSubstPrefix = "criticalPairs: substitution failure: "

fatalSubstError :: Text -> Text
fatalSubstError err = fatalSubstPrefix <> err

isFatalSubstError :: Text -> Bool
isFatalSubstError = T.isPrefixOf fatalSubstPrefix


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
  , piTySubst :: Subst
  , piAttrSubst :: AttrSubst
  } deriving (Eq, Show)

criticalPairsForDoctrine :: CPMode -> RewritePolicy -> Doctrine -> Either Text [CriticalPairInfo]
criticalPairsForDoctrine mode policy doc =
  criticalPairsForRulesTT (doctrineTypeTheory doc) mode (rulesWithClass policy (dCells2 doc))

criticalPairsForRules :: ModeTheory -> CPMode -> [RuleInfo] -> Either Text [CriticalPairInfo]
criticalPairsForRules mt mode rules =
  criticalPairsForRulesTT (modeOnlyTypeTheory mt) mode rules

criticalPairsForRulesTT :: TypeTheory -> CPMode -> [RuleInfo] -> Either Text [CriticalPairInfo]
criticalPairsForRulesTT tt mode rules = do
  let numbered = zip [0 :: Int ..] rules
  let pairs =
        [ (r1, r2)
        | (i, r1) <- numbered
        , (j, r2) <- numbered
        , i <= j
        , allowedPairSym mode r1 r2
        ]
  pairsOut <- fmap concat (mapM (uncurry (criticalPairsForPair tt)) pairs)
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

criticalPairsForPair :: TypeTheory -> RuleInfo -> RuleInfo -> Either Text [CriticalPairInfo]
criticalPairsForPair tt r1 r2 = do
  let r1' = renameRule 0 (riRule r1)
  let r2' = renameRule 1 (riRule r2)
  let tyFlex = S.fromList (rrTyVars r1' <> rrTyVars r2')
  let tmFlex =
        S.union
          (freeTmVarsDiagram (rrLHS r1'))
          (freeTmVarsDiagram (rrLHS r2'))
  let attrFlex =
        S.union
          (freeAttrVarsDiagram (rrLHS r1'))
          (freeAttrVarsDiagram (rrLHS r2'))
  overlaps <- enumerateOverlaps tt tyFlex tmFlex attrFlex (rrLHS r1') (rrLHS r2')
  fmap concat (mapM (buildPair r1 r2 r1' r2') overlaps)
  where
    buildPair r1Info r2Info rule1 rule2 ov = do
      (host, match1, match2) <- buildOverlapHost tt (rrLHS rule1) (rrLHS rule2) ov
      if danglingOk (rrLHS rule1) host match1 && danglingOk (rrLHS rule2) host match2
        then do
          left <- applyRuleAtMatch tt rule1 match1 host
          right <- applyRuleAtMatch tt rule2 match2 host
          overlap' <- canonDiagramRaw host
          left' <- canonDiagramRaw left
          right' <- canonDiagramRaw right
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
            , rrTmVars = c2TmVars cell
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

renameRule :: Int -> RewriteRule -> RewriteRule
renameRule idx rule =
  let idxText = T.pack (show idx)
      tySuffix = ":" <> idxText
      tmSuffix = "$" <> idxText
      attrSuffix = "#" <> idxText
      binderSuffix = "%" <> idxText
      renamedTyVars = M.fromList [ (v, renameTyVar v) | v <- rrTyVars rule ]
      renameTyVar v = v { tvName = tvName v <> tySuffix }
      renameBinderMeta (BinderMetaVar name) = BinderMetaVar (name <> binderSuffix)
      renameTyNode ty =
        case ty of
          TVar v ->
            case M.lookup v renamedTyVars of
              Just v' -> TVar v'
              Nothing -> TVar v
          _ -> ty
      renameTmVar v =
        v
          { tmvName = tmvName v <> tmSuffix
          , tmvSort = renameTmType (tmvSort v)
          }
      renameTmTerm (TermDiagram diag) =
        TermDiagram $
          runIdentity $
            traverseDiagram onDiag onPayload pure diag
        where
          onDiag d =
            pure d
              { dPortTy = IM.map renameTmType (dPortTy d)
              , dTmCtx = map renameTmType (dTmCtx d)
              }
          onPayload payload =
            pure $
              case payload of
                PTmMeta v -> PTmMeta (renameTmVar v)
                _ -> payload
      renameTmType ty = mapTypeExpr renameTyNode renameTmTerm ty
      lhsTm' = renameTmVarsDiagram renameTmType (rrLHS rule)
      rhsTm' = renameTmVarsDiagram renameTmType (rrRHS rule)
      lhsB' = renameBinderMetasDiagram renameBinderMeta lhsTm'
      rhsB' = renameBinderMetasDiagram renameBinderMeta rhsTm'
      lhs' = renameAttrVarsDiagram (<> attrSuffix) lhsB'
      rhs' = renameAttrVarsDiagram (<> attrSuffix) rhsB'
      tyvars' = map renameTyVar (rrTyVars rule)
      tmVars' = map renameTmVar (rrTmVars rule)
  in rule { rrLHS = lhs', rrRHS = rhs', rrTyVars = tyvars', rrTmVars = tmVars' }

enumerateOverlaps :: TypeTheory -> S.Set TyVar -> S.Set TmVar -> S.Set AttrVar -> Diagram -> Diagram -> Either Text [PartialIso]
enumerateOverlaps tt tyFlex tmFlex attrFlex l1 l2 =
  if dMode l1 /= dMode l2 || dTmCtx l1 /= dTmCtx l2
    then Right []
    else do
      let edges1 = sortEdges (IM.elems (dEdges l1))
      let edges2 = sortEdges (IM.elems (dEdges l2))
      fmap concat (mapM (seedFrom edges2) edges1)
  where
    emptyState = PartialIso M.empty M.empty S.empty S.empty U.emptySubst M.empty
    seedFrom edges2 e1 =
      fmap concat (mapM (expandFromSeed e1) edges2)
    expandFromSeed e1 e2 = do
      seeds <- mapEdge tt tyFlex tmFlex attrFlex l1 l2 emptyState e1 e2
      fmap concat (mapM (expandState tt l1 l2 tyFlex tmFlex attrFlex) seeds)

expandState :: TypeTheory -> Diagram -> Diagram -> S.Set TyVar -> S.Set TmVar -> S.Set AttrVar -> PartialIso -> Either Text [PartialIso]
expandState tt l1 l2 tyFlex tmFlex attrFlex st = do
  let mappedPorts = S.fromList (M.keys (piPortMap st))
  let candidates =
        [ e
        | e <- sortEdges (IM.elems (dEdges l1))
        , M.notMember (eId e) (piEdgeMap st)
        , any (`S.member` mappedPorts) (eIns e <> eOuts e)
        ]
  expanded <- fmap concat (mapM (expandEdge tt l1 l2 tyFlex tmFlex attrFlex st) candidates)
  deeper <- fmap concat (mapM (expandState tt l1 l2 tyFlex tmFlex attrFlex) expanded)
  pure (st : deeper)

expandEdge :: TypeTheory -> Diagram -> Diagram -> S.Set TyVar -> S.Set TmVar -> S.Set AttrVar -> PartialIso -> Edge -> Either Text [PartialIso]
expandEdge tt l1 l2 tyFlex tmFlex attrFlex st e1 = do
  let candidates =
        [ e2
        | e2 <- sortEdges (IM.elems (dEdges l2))
        , eId e2 `S.notMember` piUsedEdges st
        , edgeCompatible e1 e2
        ]
  fmap concat (mapM (mapEdge tt tyFlex tmFlex attrFlex l1 l2 st e1) candidates)

mapEdge :: TypeTheory -> S.Set TyVar -> S.Set TmVar -> S.Set AttrVar -> Diagram -> Diagram -> PartialIso -> Edge -> Edge -> Either Text [PartialIso]
mapEdge tt tyFlex tmFlex attrFlex l1 l2 st e1 e2 =
  if M.member (eId e1) (piEdgeMap st)
    then Right []
    else if eId e2 `S.member` piUsedEdges st
    then Right []
    else if length (eIns e1) /= length (eIns e2) || length (eOuts e1) /= length (eOuts e2)
      then Right []
      else do
        substs <- payloadSubsts tt tyFlex tmFlex attrFlex (piTySubst st) (piAttrSubst st) (ePayload e1) (ePayload e2)
        fmap concat (mapM extendPorts substs)
  where
    extendPorts (tySubst0, attrSubst0) = do
      let pairs = zip (eIns e1) (eIns e2) <> zip (eOuts e1) (eOuts e2)
      case foldl (extendPort tt l1 l2 tyFlex tmFlex) (Right (piPortMap st, piUsedPorts st, tySubst0, attrSubst0)) pairs of
        Left err ->
          if isFatalSubstError err
            then Left err
            else Right []
        Right (portMap', usedPorts', tySubst', attrSubst') -> do
          let edgeMap' = M.insert (eId e1) (eId e2) (piEdgeMap st)
          let usedEdges' = S.insert (eId e2) (piUsedEdges st)
          pure
            [ st
                { piEdgeMap = edgeMap'
                , piPortMap = portMap'
                , piUsedEdges = usedEdges'
                , piUsedPorts = usedPorts'
                , piTySubst = tySubst'
                , piAttrSubst = attrSubst'
                }
            ]

extendPort :: TypeTheory -> Diagram -> Diagram -> S.Set TyVar -> S.Set TmVar -> Either Text (M.Map PortId PortId, S.Set PortId, Subst, AttrSubst) -> (PortId, PortId) -> Either Text (M.Map PortId PortId, S.Set PortId, Subst, AttrSubst)
extendPort tt l1 l2 flex tmFlex acc (p1, p2) = do
  (portMap, usedPorts, tySubst, attrSubst) <- acc
  case M.lookup p1 portMap of
    Just p2' ->
      if p2' == p2 then Right (portMap, usedPorts, tySubst, attrSubst) else Left "criticalPairs: port mapping conflict"
    Nothing ->
      if p2 `S.member` usedPorts
        then Left "criticalPairs: target port already used"
        else do
          s1 <- unifyPorts tt l1 l2 flex tmFlex tySubst p1 p2
          tySubst' <- mapLeft fatalSubstError (U.composeSubst tt s1 tySubst)
          Right (M.insert p1 p2 portMap, S.insert p2 usedPorts, tySubst', attrSubst)

unifyPorts :: TypeTheory -> Diagram -> Diagram -> S.Set TyVar -> S.Set TmVar -> Subst -> PortId -> PortId -> Either Text Subst
unifyPorts tt l1 l2 flex tmFlex subst p1 p2 = do
  pTy <- requirePortType l1 p1
  hTy <- requirePortType l2 p2
  pTy' <- mapLeft fatalSubstError (U.applySubstTy tt subst pTy)
  hTy' <- mapLeft fatalSubstError (U.applySubstTy tt subst hTy)
  tmCtx' <- mapLeft fatalSubstError (U.applySubstCtx tt subst (dTmCtx l1))
  U.unifyTyFlex
    tt
    tmCtx'
    flex
    tmFlex
    U.emptySubst
    pTy'
    hTy'

payloadSubsts :: TypeTheory -> S.Set TyVar -> S.Set TmVar -> S.Set AttrVar -> Subst -> AttrSubst -> EdgePayload -> EdgePayload -> Either Text [(Subst, AttrSubst)]
payloadSubsts tt tyFlex tmFlex attrFlex tySubst attrSubst p1 p2 =
  case (p1, p2) of
    (PGen g1 attrs1 bargs1, PGen g2 attrs2 bargs2) ->
      if g1 /= g2 || M.keysSet attrs1 /= M.keysSet attrs2 || length bargs1 /= length bargs2
        then Right []
        else do
          case foldl unifyField (Right attrSubst) (M.toList attrs1) of
            Left _ -> Right []
            Right attrSubst' ->
              foldl step (Right [(tySubst, attrSubst')]) (zip bargs1 bargs2)
      where
        unifyField acc (field, term1) = do
          sub <- acc
          case M.lookup field attrs2 of
            Nothing -> Left "criticalPairs: missing attribute field"
            Just term2 -> unifyAttrFlex attrFlex sub term1 term2
        step acc pair = do
          subs <- acc
          fmap concat (mapM (\(tyS, attrS) -> binderArgSubsts tyS attrS pair) subs)

        binderArgSubsts tySubst0 attrSubst0 (lhsArg, rhsArg) =
          case (lhsArg, rhsArg) of
            (BAConcrete d1, BAConcrete d2) ->
              fmap
                (map (\(tySub', attrSub') -> (tySub', attrSub')))
                ( mapLeft
                    fatalSubstError
                    (Strat.Poly.Graph.diagramIsoMatchWithVarsFrom tt tyFlex tmFlex attrFlex tySubst0 attrSubst0 d1 d2)
                )
            (BAMeta x, BAMeta y) ->
              if x == y then Right [(tySubst0, attrSubst0)] else Right []
            _ -> Right []
    (PBox _ d1, PBox _ d2) -> do
      mapLeft
        fatalSubstError
        (Strat.Poly.Graph.diagramIsoMatchWithVarsFrom tt tyFlex tmFlex attrFlex tySubst attrSubst d1 d2)
    (PFeedback d1, PFeedback d2) ->
      mapLeft
        fatalSubstError
        (Strat.Poly.Graph.diagramIsoMatchWithVarsFrom tt tyFlex tmFlex attrFlex tySubst attrSubst d1 d2)
    (PSplice x, PSplice y) | x == y -> Right [(tySubst, attrSubst)]
    (PTmMeta x, PTmMeta y)
      | tmvName x == tmvName y && tmvScope x == tmvScope y -> Right [(tySubst, attrSubst)]
    (PInternalDrop, PInternalDrop) -> Right [(tySubst, attrSubst)]
    _ -> Right []

edgeCompatible :: Edge -> Edge -> Bool
edgeCompatible e1 e2 =
  length (eIns e1) == length (eIns e2)
    && length (eOuts e1) == length (eOuts e2)
    && payloadCompatible (ePayload e1) (ePayload e2)

payloadCompatible :: EdgePayload -> EdgePayload -> Bool
payloadCompatible p1 p2 =
  case (p1, p2) of
    (PGen g1 attrs1 bargs1, PGen g2 attrs2 bargs2) ->
      g1 == g2 && M.keysSet attrs1 == M.keysSet attrs2 && length bargs1 == length bargs2
    (PBox _ _, PBox _ _) -> True
    (PFeedback _, PFeedback _) -> True
    (PSplice x, PSplice y) -> x == y
    (PTmMeta x, PTmMeta y) -> tmvName x == tmvName y && tmvScope x == tmvScope y
    (PInternalDrop, PInternalDrop) -> True
    _ -> False

sortEdges :: [Edge] -> [Edge]
sortEdges = L.sortOn (unEdgeId . eId)

requirePortType :: Diagram -> PortId -> Either Text TypeExpr
requirePortType diag pid =
  case diagramPortType diag pid of
    Nothing -> Left "criticalPairs: missing port type"
    Just ty -> Right ty

buildOverlapHost :: TypeTheory -> Diagram -> Diagram -> PartialIso -> Either Text (Diagram, Match, Match)
buildOverlapHost tt l1 l2 ov = do
  let tySubst = piTySubst ov
  let attrSubst = piAttrSubst ov
  l1' <- applySubstsDiagramLocal tt tySubst attrSubst l1
  l2' <- applySubstsDiagramLocal tt tySubst attrSubst l2
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
  let m1 = mkIdentityMatch tySubst attrSubst l1'
  let m2 = mkMatchForL2 tySubst attrSubst l2' portMap2 edgeMap1
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

mkIdentityMatch :: Subst -> AttrSubst -> Diagram -> Match
mkIdentityMatch tySubst attrSubst diag =
  let ports = diagramPortIds diag
      edges = IM.elems (dEdges diag)
      mPorts = M.fromList [ (p, p) | p <- ports ]
      mEdges = M.fromList [ (eId e, eId e) | e <- edges ]
      usedPorts = S.fromList ports
      usedEdges = S.fromList (map eId edges)
  in
    Match
      { mPortMap = mPorts
      , mEdgeMap = mEdges
      , mTySubst = tySubst
      , mAttrSubst = attrSubst
      , mBinderSub = M.empty
      , mUsedHostPorts = usedPorts
      , mUsedHostEdges = usedEdges
      }

mkMatchForL2 :: Subst -> AttrSubst -> Diagram -> M.Map PortId PortId -> M.Map EdgeId EdgeId -> Match
mkMatchForL2 tySubst attrSubst l2 portMap edgeMap =
  let ports = diagramPortIds l2
      edges = IM.elems (dEdges l2)
      mPorts = M.fromList [ (p, M.findWithDefault p p portMap) | p <- ports ]
      mEdges = M.fromList [ (eId e, M.findWithDefault (eId e) (eId e) edgeMap) | e <- edges ]
      usedPorts = S.fromList (M.elems mPorts)
      usedEdges = S.fromList (M.elems mEdges)
  in
    Match
      { mPortMap = mPorts
      , mEdgeMap = mEdges
      , mTySubst = tySubst
      , mAttrSubst = attrSubst
      , mBinderSub = M.empty
      , mUsedHostPorts = usedPorts
      , mUsedHostEdges = usedEdges
      }

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
    portKey = unPortId

applyRuleAtMatch :: TypeTheory -> RewriteRule -> Match -> Diagram -> Either Text Diagram
applyRuleAtMatch tt rule match host = do
  let lhs = rrLHS rule
  rhs <- applySubstsDiagramLocal tt (mTySubst match) (mAttrSubst match) (rrRHS rule)
  host1 <- deleteMatchedEdges host (M.elems (mEdgeMap match))
  host2 <- deleteMatchedPorts host1 (internalPorts lhs) (mPortMap match)
  let rhsShift = shiftDiagram (dNextPort host2) (dNextEdge host2) rhs
  host3 <- unionDiagram host2 rhsShift
  let lhsBoundary = dIn lhs <> dOut lhs
  let rhsBoundary = dIn rhsShift <> dOut rhsShift
  if length lhsBoundary /= length rhsBoundary
    then Left "criticalPairs: boundary length mismatch"
    else do
      boundaryPairs <- mapM toBoundaryPair (zip lhsBoundary rhsBoundary)
      host4 <- mergeBoundaryPairs host3 boundaryPairs
      validateDiagram host4
      pure host4
  where
    toBoundaryPair (lhsPort, rhsPort) =
      case M.lookup lhsPort (mPortMap match) of
        Nothing -> Left "criticalPairs: missing boundary port mapping"
        Just hostPort -> Right (hostPort, rhsPort)

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
      deleteEdgeKeepPorts d eid

deleteMatchedPorts :: Diagram -> [PortId] -> M.Map PortId PortId -> Either Text Diagram
deleteMatchedPorts diag ports portMap = foldl step (Right diag) ports
  where
    step acc p = do
      d <- acc
      case M.lookup p portMap of
        Nothing -> Left "criticalPairs: missing port mapping"
        Just hostPort -> deletePortIfDangling d hostPort

applySubstsDiagramLocal :: TypeTheory -> Subst -> AttrSubst -> Diagram -> Either Text Diagram
applySubstsDiagramLocal tt tySubst attrSubst diag = do
  dTy <- mapLeft fatalSubstError (Diag.applySubstDiagram tt tySubst diag)
  pure (applyAttrSubstDiagram attrSubst dTy)

renameTmVarsDiagram :: (TypeExpr -> TypeExpr) -> Diagram -> Diagram
renameTmVarsDiagram renameTy =
  runIdentity . traverseDiagram onDiag onPayload pure
  where
    onDiag d =
      pure d
        { dPortTy = IM.map renameTy (dPortTy d)
        , dTmCtx = map renameTy (dTmCtx d)
        }
    onPayload payload =
      pure $
        case payload of
          PTmMeta v -> PTmMeta v { tmvSort = renameTy (tmvSort v) }
          _ -> payload

renameBinderMetasDiagram :: (BinderMetaVar -> BinderMetaVar) -> Diagram -> Diagram
renameBinderMetasDiagram renameMeta =
  runIdentity . traverseDiagram pure onPayload onBArg
  where
    onPayload payload =
      pure $
        case payload of
          PSplice x -> PSplice (renameMeta x)
          _ -> payload

    onBArg barg =
      pure $
        case barg of
          BAMeta x -> BAMeta (renameMeta x)
          _ -> barg

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

mapLeft :: (e -> e') -> Either e a -> Either e' a
mapLeft f res =
  case res of
    Left err -> Left (f err)
    Right x -> Right x
