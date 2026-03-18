{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Rewrite
  ( RewriteRule(..)
  , RewriteProgress(..)
  , SpliceMapper
  , defaultSpliceMapper
  , rewriteOnceRawDetailedWithMapper
  , rewriteOnceRawWithMapper
  , rewriteOnceRaw
  , rewriteOnceWithMapper
  , rewriteOnce
  , rewriteAllWithMapper
  , rewriteAll
  , rewriteAllNested
  , applyMatchWithMapper
  , applyMatch
  , instantiateBinderMetas
  , expandSplices
  , mkMatchConfig
  , rulesFromPolicy
  , rulesForMode
  , rulesForDiagram
  ) where

import Data.Text (Text)
import qualified Data.IntMap.Strict as IM
import qualified Data.List as L
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Monoid (Any(..), getAny)
import Strat.Poly.Graph
import Strat.Poly.Diagram hiding (applySubstDiagram)
import Strat.Poly.Match
import Strat.Poly.ObjEq (ObjEqInCtx)
import Strat.Poly.Obj (Obj, TmVar(..), TermDiagram(..))
import Strat.Poly.Cell2
import Strat.Poly.Term.RuleDiagram (SpliceMapper, expandSplices, instantiateBinderMetas, sameModeSpliceMapper)
import Strat.Poly.Subst (emptySubst)
import Strat.Poly.Term.SubstRuntime (applySubstCtx, applySubstDiagram, applySubstObj)
import Strat.Common.Rules (RewritePolicy(..))
import Strat.Common.Rules (Orientation(..), RuleClass(..))
import Strat.Poly.ModeSyntax (ModeName)
import Strat.Poly.Syntax (CodeArg(..))
import Strat.Poly.TypeTheory (TypeTheory, diagramRulesForMode)
import Strat.Poly.Traversal (foldDiagram, traverseDiagram)


data RewriteRule = RewriteRule
  { rrName   :: Text
  , rrLHS    :: Diagram
  , rrRHS    :: Diagram
  , rrTyVars :: [TmVar]
  , rrTmVars :: [TmVar]
  } deriving (Eq, Show)

data RewriteProgress = RewriteProgress
  { rpDiagram :: Diagram
  , rpTouchedEdges :: S.Set EdgeId
  } deriving (Eq, Show)

defaultSpliceMapper :: SpliceMapper
defaultSpliceMapper =
  sameModeSpliceMapper "rewriteOnce"

rewriteOnceRawDetailedWithMapper
  :: ObjEqInCtx
  -> TypeTheory
  -> SpliceMapper
  -> Maybe (S.Set EdgeId)
  -> [RewriteRule]
  -> Diagram
  -> Either Text (Maybe RewriteProgress)
rewriteOnceRawDetailedWithMapper objEq tt spliceMapper mSeedEdges rules diag = do
  top <- rewriteOnceTopRawDetailed objEq tt spliceMapper mSeedEdges rules diag
  case top of
    Just _ -> pure top
    Nothing -> rewriteOnceNestedRawDetailed objEq tt spliceMapper mSeedEdges rules diag

rewriteOnceRawWithMapper :: ObjEqInCtx -> TypeTheory -> SpliceMapper -> [RewriteRule] -> Diagram -> Either Text (Maybe Diagram)
rewriteOnceRawWithMapper objEq tt spliceMapper rules diag =
  fmap (fmap rpDiagram) (rewriteOnceRawDetailedWithMapper objEq tt spliceMapper Nothing rules diag)

rewriteOnceRaw :: ObjEqInCtx -> TypeTheory -> [RewriteRule] -> Diagram -> Either Text (Maybe Diagram)
rewriteOnceRaw objEq tt =
  rewriteOnceRawWithMapper objEq tt defaultSpliceMapper

rewriteOnceWithMapper :: ObjEqInCtx -> TypeTheory -> SpliceMapper -> [RewriteRule] -> Diagram -> Either Text (Maybe Diagram)
rewriteOnceWithMapper objEq tt spliceMapper rules diag =
  rewriteOnceRawWithMapper objEq tt spliceMapper rules diag

rewriteOnce :: ObjEqInCtx -> TypeTheory -> [RewriteRule] -> Diagram -> Either Text (Maybe Diagram)
rewriteOnce objEq tt =
  rewriteOnceRaw objEq tt

rewriteOnceTopRawDetailed
  :: ObjEqInCtx
  -> TypeTheory
  -> SpliceMapper
  -> Maybe (S.Set EdgeId)
  -> [RewriteRule]
  -> Diagram
  -> Either Text (Maybe RewriteProgress)
rewriteOnceTopRawDetailed objEq tt spliceMapper mSeedEdges rules diag
  | maybe False S.null mSeedEdges = Right Nothing
  | otherwise =
      let hostIndex = buildHostIndex diag
       in go hostIndex rules
  where
    go _ [] = Right Nothing
    go hostIndex (r:rs) = do
      widenedRule <-
        case widenRuleToHostTmCtx diag r of
          Left _ -> Right Nothing
          Right one -> Right (Just one)
      case widenedRule of
        Nothing -> go hostIndex rs
        Just r'
          | dMode (rrLHS r') /= dMode diag -> go hostIndex rs
          | otherwise -> do
              rejectSplice "rewrite rule lhs" (rrLHS r')
              result <-
                case mSeedEdges of
                  Nothing ->
                    findFirstSuccessfulMatchWithIndex
                      (mkMatchConfig objEq tt r')
                      (rrLHS r')
                      hostIndex
                      diag
                      (\m ->
                          case applyMatchDetailedWithMapper tt spliceMapper r' m diag of
                            Left _ -> Right Nothing
                            Right progress -> Right (Just progress)
                      )
                  Just seedEdges ->
                    findFirstSuccessfulMatchWithIndexSeeded
                      (mkMatchConfig objEq tt r')
                      (rrLHS r')
                      hostIndex
                      seedEdges
                      diag
                      (\m ->
                          case applyMatchDetailedWithMapper tt spliceMapper r' m diag of
                            Left _ -> Right Nothing
                            Right progress -> Right (Just progress)
                      )
              case result of
                Just progress -> Right (Just progress)
                Nothing -> go hostIndex rs

rewriteOnceNestedRawDetailed
  :: ObjEqInCtx
  -> TypeTheory
  -> SpliceMapper
  -> Maybe (S.Set EdgeId)
  -> [RewriteRule]
  -> Diagram
  -> Either Text (Maybe RewriteProgress)
rewriteOnceNestedRawDetailed objEq tt spliceMapper mSeedEdges rules diag
  | maybe False S.null mSeedEdges = Right Nothing
  | otherwise =
      go scopedEdges
  where
    scopedEdges =
      let edges = IM.toAscList (dEdges diag)
       in case mSeedEdges of
            Nothing -> edges
            Just seedEdges -> filter (\(edgeKey, _) -> EdgeId edgeKey `S.member` seedEdges) edges

    rulesByMode =
      M.fromListWith (<>) [(dMode (rrLHS rule), [rule]) | rule <- rules]

    nestedRules inner =
      M.findWithDefault [] (dMode inner) rulesByMode

    go [] = Right Nothing
    go ((edgeKey, edge):rest) =
      case ePayload edge of
        PSplice _ _ -> go rest
        PProvider _ -> go rest
        PModuleRef _ -> go rest
        PBox name inner -> do
          case nestedRules inner of
            [] -> go rest
            innerRules -> do
              innerRes <- rewriteOnceRawDetailedWithMapper objEq tt spliceMapper Nothing innerRules inner
              case innerRes of
                Nothing -> go rest
                Just progress -> do
                  let inner' = rpDiagram progress
                  let edge' = edge { ePayload = PBox name inner' }
                  let diag' = diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
                  pure (Just (RewriteProgress diag' (localTouchedEdges diag' edge')))
        PFeedback inner -> do
          case nestedRules inner of
            [] -> go rest
            innerRules -> do
              innerRes <- rewriteOnceRawDetailedWithMapper objEq tt spliceMapper Nothing innerRules inner
              case innerRes of
                Nothing -> go rest
                Just progress -> do
                  let inner' = rpDiagram progress
                  let edge' = edge { ePayload = PFeedback inner' }
                  let diag' = diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
                  pure (Just (RewriteProgress diag' (localTouchedEdges diag' edge')))
        PTmMeta _ ->
          go rest
        PTmLit _ ->
          go rest
        PInternalDrop ->
          go rest
        PGen gen args bargs -> do
          argRes <- rewriteOnceCodeArgs args
          case argRes of
            Just args' -> do
              let edge' = edge { ePayload = PGen gen args' bargs }
              let diag' = diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
              pure (Just (RewriteProgress diag' (localTouchedEdges diag' edge')))
            Nothing -> do
              bargRes <- rewriteOnceBinderArgs bargs
              case bargRes of
                Nothing -> go rest
                Just bargs' -> do
                  let edge' = edge { ePayload = PGen gen args bargs' }
                  let diag' = diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
                  pure (Just (RewriteProgress diag' (localTouchedEdges diag' edge')))

    rewriteOnceCodeArgs [] = Right Nothing
    rewriteOnceCodeArgs (arg:args) =
      case arg of
        CAObj _ -> fmap (fmap (arg :)) (rewriteOnceCodeArgs args)
        CATm (TermDiagram inner) -> do
          case nestedRules inner of
            [] -> fmap (fmap (arg :)) (rewriteOnceCodeArgs args)
            innerRules -> do
              res <- rewriteOnceRawDetailedWithMapper objEq tt spliceMapper Nothing innerRules inner
              case res of
                Just progress ->
                  let inner' = rpDiagram progress
                   in Right (Just (CATm (TermDiagram inner') : args))
                Nothing -> fmap (fmap (arg :)) (rewriteOnceCodeArgs args)

    rewriteOnceBinderArgs [] = Right Nothing
    rewriteOnceBinderArgs (b:bs) =
      case b of
        BAMeta _ -> fmap (fmap (b :)) (rewriteOnceBinderArgs bs)
        BAConcrete inner -> do
          case nestedRules inner of
            [] -> fmap (fmap (b :)) (rewriteOnceBinderArgs bs)
            innerRules -> do
              res <- rewriteOnceRawDetailedWithMapper objEq tt spliceMapper Nothing innerRules inner
              case res of
                Just progress ->
                  let inner' = rpDiagram progress
                   in Right (Just (BAConcrete inner' : bs))
                Nothing -> fmap (fmap (b :)) (rewriteOnceBinderArgs bs)

    localTouchedEdges current edge =
      S.insert (eId edge) (incidentEdges current (S.fromList (eIns edge <> eOuts edge)))

rewriteAllWithMapper :: ObjEqInCtx -> TypeTheory -> SpliceMapper -> Int -> [RewriteRule] -> Diagram -> Either Text [Diagram]
rewriteAllWithMapper objEq tt spliceMapper cap rules diag = do
  top <- rewriteAllTop objEq tt spliceMapper rules diag
  inner <- rewriteAllNested objEq tt spliceMapper cap rules diag
  pure (take cap (top <> inner))
  where
    rewriteAllTop objEq' tt' spliceMapper' rules' diag' = go [] rules'
      where
        go acc [] = Right acc
        go acc (r:rs) = do
          widenedRule <-
            case widenRuleToHostTmCtx diag' r of
              Left _ -> Right Nothing
              Right one -> Right (Just one)
          case widenedRule of
            Nothing -> go acc rs
            Just r'
              | dMode (rrLHS r') /= dMode diag' -> go acc rs
              | otherwise -> do
                  matches <- findAllMatches (mkMatchConfig objEq' tt' r') (rrLHS r') diag'
                  applied <- foldl (collect r') (Right []) matches
                  go (acc <> applied) rs
          where
            collect r' acc m =
              case acc of
                Left err -> Left err
                Right ds ->
                  case applyMatchWithMapper tt' spliceMapper' r' m diag' of
                    Left _ -> Right ds
                    Right d -> Right (ds <> [d])

rewriteAll :: ObjEqInCtx -> TypeTheory -> Int -> [RewriteRule] -> Diagram -> Either Text [Diagram]
rewriteAll objEq tt =
  rewriteAllWithMapper objEq tt defaultSpliceMapper

rewriteAllNested :: ObjEqInCtx -> TypeTheory -> SpliceMapper -> Int -> [RewriteRule] -> Diagram -> Either Text [Diagram]
rewriteAllNested objEq tt spliceMapper cap rules diag = do
  let edges = IM.toAscList (dEdges diag)
  fmap concat (mapM (rewriteInEdge objEq tt spliceMapper cap rules diag) edges)

rewriteInEdge :: ObjEqInCtx -> TypeTheory -> SpliceMapper -> Int -> [RewriteRule] -> Diagram -> (Int, Edge) -> Either Text [Diagram]
rewriteInEdge objEq tt spliceMapper cap rules diag (edgeKey, edge) =
  case ePayload edge of
    PSplice _ _ -> Right []
    PProvider _ -> Right []
    PModuleRef _ -> Right []
    PBox name inner -> do
      innerRes <- rewriteAllWithMapper objEq tt spliceMapper cap rules inner
      mapM
        (\d ->
          let edge' = edge { ePayload = PBox name d }
              diag' = diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
           in Right diag')
        innerRes
    PFeedback inner -> do
      innerRes <- rewriteAllWithMapper objEq tt spliceMapper cap rules inner
      mapM
        (\d ->
          let edge' = edge { ePayload = PFeedback d }
              diag' = diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
           in Right diag')
        innerRes
    PTmMeta _ ->
      Right []
    PTmLit _ ->
      Right []
    PInternalDrop ->
      Right []
    PGen gen args bargs -> do
      argsRes <- rewriteAllCodeArgs objEq tt spliceMapper cap rules args
      fromArgs <-
        mapM
          (\args' ->
            let edge' = edge { ePayload = PGen gen args' bargs }
                diag' = diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
             in Right diag')
          argsRes
      bargsRes <- rewriteAllBinderArgs objEq tt spliceMapper cap rules bargs
      fromBinders <-
        mapM
          (\bargs' ->
            let edge' = edge { ePayload = PGen gen args bargs' }
                diag' = diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
             in Right diag')
          bargsRes
      pure (fromArgs <> fromBinders)

rewriteAllCodeArgs :: ObjEqInCtx -> TypeTheory -> SpliceMapper -> Int -> [RewriteRule] -> [CodeArg] -> Either Text [[CodeArg]]
rewriteAllCodeArgs _ _ _ _ _ [] = Right []
rewriteAllCodeArgs objEq tt spliceMapper cap rules args =
  fmap concat (mapM rewriteAt [0 .. length args - 1])
  where
    rewriteAt i =
      case splitAt i args of
        (pre, CATm (TermDiagram inner) : post) -> do
          res <- rewriteAllWithMapper objEq tt spliceMapper cap rules inner
          pure [pre <> [CATm (TermDiagram inner')] <> post | inner' <- res]
        _ -> Right []

rewriteAllBinderArgs :: ObjEqInCtx -> TypeTheory -> SpliceMapper -> Int -> [RewriteRule] -> [BinderArg] -> Either Text [[BinderArg]]
rewriteAllBinderArgs _ _ _ _ _ [] = Right []
rewriteAllBinderArgs objEq tt spliceMapper cap rules args =
  fmap concat (mapM rewriteAt [0 .. length args - 1])
  where
    rewriteAt i =
      case splitAt i args of
        (pre, BAConcrete inner : post) -> do
          res <- rewriteAllWithMapper objEq tt spliceMapper cap rules inner
          pure [pre <> [BAConcrete inner'] <> post | inner' <- res]
        _ -> Right []

applyMatchWithMapper :: TypeTheory -> SpliceMapper -> RewriteRule -> Match -> Diagram -> Either Text Diagram
applyMatchWithMapper tt spliceMapper rule match host =
  rpDiagram <$> applyMatchDetailedWithMapper tt spliceMapper rule match host

applyMatchDetailedWithMapper :: TypeTheory -> SpliceMapper -> RewriteRule -> Match -> Diagram -> Either Text RewriteProgress
applyMatchDetailedWithMapper tt spliceMapper rule match host = do
  let lhs = rrLHS rule
  let lhsBoundary = dIn lhs <> dOut lhs
  hostBoundary <- mapM boundaryHostPort lhsBoundary
  hostCtxNorm <- normalizeDiagramCtxOnly tt host
  hostNorm <- normalizeMergeSupport tt (S.fromList hostBoundary) hostCtxNorm
  rhs0 <- applySubstDiagram tt (mTySubst match) (rrRHS rule)
  rhs1 <- instantiateBinderMetas (mBinderSub match) rhs0
  rhs <- expandSplices spliceMapper (mBinderSub match) rhs1
  host1 <- deleteMatchedEdges hostNorm (M.elems (mEdgeMap match))
  host2 <- deleteMatchedPorts host1 (internalPorts lhs) (mPortMap match)
  let rhsShift = shiftDiagram (dNextPort host2) (dNextEdge host2) rhs
  host3 <- unionDiagram host2 rhsShift
  let rhsBoundary = dIn rhsShift <> dOut rhsShift
  if length lhsBoundary /= length rhsBoundary
    then Left "rewriteOnce: boundary length mismatch"
    else do
      boundaryPairs <- mapM toBoundaryPair (zip lhsBoundary rhsBoundary)
      host4 <- mergeBoundaryPairs host3 boundaryPairs
      host5 <- normalizeMergeSupport tt (S.fromList hostBoundary) host4
      validateDiagram host5
      pure
        RewriteProgress
          { rpDiagram = host5
          , rpTouchedEdges = affectedEdgesFromRewrite host host5 (S.fromList hostBoundary)
          }
  where
    boundaryHostPort lhsPort =
      case M.lookup lhsPort (mPortMap match) of
        Nothing -> Left "rewriteOnce: missing boundary port mapping"
        Just hostPort -> Right hostPort

    toBoundaryPair (lhsPort, rhsPort) =
      case M.lookup lhsPort (mPortMap match) of
        Nothing -> Left "rewriteOnce: missing boundary port mapping"
        Just hostPort -> Right (hostPort, rhsPort)

applyMatch :: TypeTheory -> RewriteRule -> Match -> Diagram -> Either Text Diagram
applyMatch tt =
  applyMatchWithMapper tt defaultSpliceMapper

affectedEdgesFromRewrite :: Diagram -> Diagram -> S.Set PortId -> S.Set EdgeId
affectedEdgesFromRewrite before after touchedPorts =
  let oldKeys = S.fromList (IM.keys (dEdges before))
      newKeys = S.fromList (IM.keys (dEdges after))
      inserted = S.map EdgeId (S.difference newKeys oldKeys)
      adjacent = incidentEdges after touchedPorts
   in inserted `S.union` adjacent

incidentEdges :: Diagram -> S.Set PortId -> S.Set EdgeId
incidentEdges current ports =
  S.fromList
    [ eId edge
    | edge <- IM.elems (dEdges current)
    , any (`S.member` ports) (eIns edge <> eOuts edge)
    ]

widenRuleToHostTmCtx :: Diagram -> RewriteRule -> Either Text RewriteRule
widenRuleToHostTmCtx host rule = do
  lhs' <- widenDiagramToHostTmCtx (dTmCtx host) (rrLHS rule)
  rhs' <- widenDiagramToHostTmCtx (dTmCtx host) (rrRHS rule)
  pure rule { rrLHS = lhs', rrRHS = rhs' }

widenDiagramToHostTmCtx :: [Obj] -> Diagram -> Either Text Diagram
widenDiagramToHostTmCtx tmCtxHost =
  traverseDiagram
    (alignDiagramTmCtxToHost tmCtxHost)
    pure
    pure
    pure

alignDiagramTmCtxToHost :: [Obj] -> Diagram -> Either Text Diagram
alignDiagramTmCtxToHost tmCtxHost diag
  | dTmCtx diag `L.isPrefixOf` tmCtxHost =
      Right diag { dTmCtx = tmCtxHost }
  | otherwise =
      weakenDiagramTmCtxToModePrefix tmCtxHost diag

normalizeDiagramCtxOnly :: TypeTheory -> Diagram -> Either Text Diagram
normalizeDiagramCtxOnly tt =
  traverseDiagram onDiag pure pure pure
  where
    onDiag d = do
      tmCtx' <- applySubstCtx tt emptySubst (dTmCtx d)
      pure d { dTmCtx = tmCtx' }

normalizeDiagramObjsOnly :: TypeTheory -> Diagram -> Either Text Diagram
normalizeDiagramObjsOnly tt =
  traverseDiagram onDiag onPayload onCodeArg pure
  where
    onDiag d = do
      dPortObj' <- IM.traverseWithKey (\_ ty -> applySubstObj tt emptySubst ty) (dPortObj d)
      pure d { dPortObj = dPortObj' }

    onPayload payload =
      case payload of
        PTmMeta v -> do
          sort' <- applySubstObj tt emptySubst (tmvSort v)
          pure (PTmMeta (v { tmvSort = sort' }))
        _ ->
          pure payload

    onCodeArg arg =
      case arg of
        CAObj obj -> CAObj <$> applySubstObj tt emptySubst obj
        CATm tm -> pure (CATm tm)

normalizeMergeSupport :: TypeTheory -> S.Set PortId -> Diagram -> Either Text Diagram
normalizeMergeSupport tt seedPorts diag = do
  let affectedPorts = closeAffectedPorts seedPorts
  let affectedMetaKeys = metaKeysForPorts affectedPorts
  dPortObj' <-
    IM.traverseWithKey
      (\k ty ->
        if PortId k `S.member` affectedPorts
          then applySubstObj tt emptySubst ty
          else Right ty
      )
      (dPortObj diag)
  dEdges' <- IM.traverseWithKey (\_ edge -> normalizeEdge affectedPorts affectedMetaKeys edge) (dEdges diag)
  pure diag { dPortObj = dPortObj', dEdges = dEdges' }
  where
    closeAffectedPorts ports =
      let ports' = ports `S.union` affectedMetaPorts ports `S.union` affectedStructuredPorts ports
       in if ports' == ports
            then ports
            else closeAffectedPorts ports'

    affectedMetaPorts ports =
      let keys = metaKeysForPorts ports
       in S.fromList
            [ pid
            | edge <- IM.elems (dEdges diag)
            , PTmMeta v <- [ePayload edge]
            , tmVarKey v `S.member` keys
            , pid <- eOuts edge
            ]

    affectedStructuredPorts ports =
      S.fromList
        [ pid
        | edge <- IM.elems (dEdges diag)
        , isStructuredEdge edge
        , edgeTouches ports edge
        , pid <- eIns edge <> eOuts edge
        ]

    metaKeysForPorts ports =
      S.fromList
        [ tmVarKey v
        | edge <- IM.elems (dEdges diag)
        , PTmMeta v <- [ePayload edge]
        , any (`S.member` ports) (eOuts edge)
        ]

    normalizeEdge ports metaKeys edge =
      case ePayload edge of
        PBox name inner
          | edgeTouches ports edge ->
              (\inner' -> edge { ePayload = PBox name inner' }) <$> normalizeDiagramObjsOnly tt inner
        PFeedback inner
          | edgeTouches ports edge ->
              (\inner' -> edge { ePayload = PFeedback inner' }) <$> normalizeDiagramObjsOnly tt inner
        PTmMeta v
          | tmVarKey v `S.member` metaKeys -> do
              sort' <- applySubstObj tt emptySubst (tmvSort v)
              pure edge { ePayload = PTmMeta (v { tmvSort = sort' }) }
        _ ->
          pure edge

    edgeTouches ports edge =
      any (`S.member` ports) (eIns edge <> eOuts edge)

    isStructuredEdge edge =
      case ePayload edge of
        PBox _ _ -> True
        PFeedback _ -> True
        _ -> False

    tmVarKey v = (tmvName v, tmvScope v)

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
        Nothing -> Left "rewriteOnce: missing port mapping"
        Just hostPort -> deletePortIfDangling d hostPort

rulesFromPolicy :: RewritePolicy -> [Cell2] -> [RewriteRule]
rulesFromPolicy policy cells = concatMap (rulesForCell policy) cells

rulesForMode :: RewritePolicy -> TypeTheory -> ModeName -> [RewriteRule]
rulesForMode policy tt mode =
  rulesFromPolicy policy (diagramRulesForMode tt mode)

rulesForDiagram :: RewritePolicy -> TypeTheory -> Diagram -> [RewriteRule]
rulesForDiagram policy tt diag =
  rulesForMode policy tt (dMode diag)

rulesForCell :: RewritePolicy -> Cell2 -> [RewriteRule]
rulesForCell policy cell =
  case policy of
    UseStructuralAsBidirectional ->
      case c2Class cell of
        Structural -> both
        Computational -> oriented
    UseOnlyComputationalLR ->
      case c2Class cell of
        Computational ->
          case c2Orient cell of
            LR -> [mk (c2LHS cell) (c2RHS cell)]
            Bidirectional -> [mk (c2LHS cell) (c2RHS cell)]
            _ -> []
        Structural -> []
    UseAllOriented -> oriented
  where
    mk lhs rhs =
      RewriteRule
        { rrName = c2Name cell
        , rrLHS = lhs
        , rrRHS = rhs
        , rrTyVars = c2TyVars cell
        , rrTmVars = c2TmVars cell
        }

    oriented =
      case c2Orient cell of
        LR -> [mk (c2LHS cell) (c2RHS cell)]
        RL -> [mk (c2RHS cell) (c2LHS cell)]
        Bidirectional -> [mk (c2LHS cell) (c2RHS cell), mk (c2RHS cell) (c2LHS cell)]
        Unoriented -> []

    both =
      [ mk (c2LHS cell) (c2RHS cell)
      , mk (c2RHS cell) (c2LHS cell)
      ]

rejectSplice :: Text -> Diagram -> Either Text ()
rejectSplice label diag =
  if hasSplice diag
    then Left (label <> ": splice nodes are not allowed in evaluation terms")
    else Right ()

hasSplice :: Diagram -> Bool
hasSplice =
  getAny . foldDiagram (\_ -> mempty) onPayload (\_ -> mempty) (\_ -> mempty)
  where
    onPayload payload =
      Any $
        case payload of
          PSplice _ _ -> True
          _ -> False

mkMatchConfig :: ObjEqInCtx -> TypeTheory -> RewriteRule -> MatchConfig
mkMatchConfig objEq tt rule =
  MatchConfig
    { mcTheory = tt
    , mcFlex = S.union (S.fromList (rrTyVars rule)) (S.fromList (rrTmVars rule))
    , mcObjEq = objEq
    }
