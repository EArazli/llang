{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Rewrite
  ( RewriteRule(..)
  , SpliceMapper
  , defaultSpliceMapper
  , rewriteOnceRawWithMapper
  , rewriteOnceRaw
  , rewriteOnceWithMapper
  , rewriteOnce
  , rewriteAllWithMapper
  , rewriteAll
  , applyMatchWithMapper
  , applyMatch
  , mkMatchConfig
  , rulesFromPolicy
  ) where

import Data.Text (Text)
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Monoid (Any(..), getAny)
import Strat.Poly.Graph
import Strat.Poly.Diagram hiding (applySubstDiagram)
import Strat.Poly.DiagramInterpretation
  ( requirePortType
  , spliceEdge
  )
import Strat.Poly.Match
import Strat.Poly.Obj (TmVar(..), TermDiagram(..))
import Strat.Poly.Cell2
import Strat.Poly.UnifyObj
  ( applySubstCtx
  , applySubstDiagram
  , applySubstObj
  , emptySubst
  )
import Strat.Common.Rules (RewritePolicy(..))
import Strat.Common.Rules (Orientation(..), RuleClass(..))
import Strat.Poly.ModeSyntax (ModExpr(..))
import Strat.Poly.Syntax (CodeArg(..))
import Strat.Poly.TypeTheory (TypeTheory)
import Strat.Poly.Traversal (foldDiagram, traverseDiagram)


data RewriteRule = RewriteRule
  { rrName   :: Text
  , rrLHS    :: Diagram
  , rrRHS    :: Diagram
  , rrTyVars :: [TmVar]
  , rrTmVars :: [TmVar]
  } deriving (Eq, Show)

type SpliceMapper = ModExpr -> Diagram -> Either Text Diagram

defaultSpliceMapper :: SpliceMapper
defaultSpliceMapper me captured =
  if null (mePath me) && meSrc me == dMode captured && meTgt me == dMode captured
    then Right captured
    else Left "rewriteOnce: splice requires modality-action mapping but no splice mapper is available"

rewriteOnceRawWithMapper :: TypeTheory -> SpliceMapper -> [RewriteRule] -> Diagram -> Either Text (Maybe Diagram)
rewriteOnceRawWithMapper tt spliceMapper rules diag = do
  rejectSplice "rewriteOnce" diag
  top <- rewriteOnceTopRaw tt spliceMapper rules diag
  case top of
    Just _ -> pure top
    Nothing -> rewriteOnceNestedRaw tt spliceMapper rules diag

rewriteOnceRaw :: TypeTheory -> [RewriteRule] -> Diagram -> Either Text (Maybe Diagram)
rewriteOnceRaw tt =
  rewriteOnceRawWithMapper tt defaultSpliceMapper

rewriteOnceWithMapper :: TypeTheory -> SpliceMapper -> [RewriteRule] -> Diagram -> Either Text (Maybe Diagram)
rewriteOnceWithMapper tt spliceMapper rules diag =
  rewriteOnceRawWithMapper tt spliceMapper rules diag

rewriteOnce :: TypeTheory -> [RewriteRule] -> Diagram -> Either Text (Maybe Diagram)
rewriteOnce tt =
  rewriteOnceRaw tt

rewriteOnceTopRaw :: TypeTheory -> SpliceMapper -> [RewriteRule] -> Diagram -> Either Text (Maybe Diagram)
rewriteOnceTopRaw tt spliceMapper rules diag = go rules
  where
    go [] = Right Nothing
    go (r:rs) = do
      if dMode (rrLHS r) /= dMode diag
        then go rs
        else do
          rejectSplice "rewrite rule lhs" (rrLHS r)
          matches <- findAllMatches (mkMatchConfig tt r) (rrLHS r) diag
          tryMatches matches
      where
        tryMatches [] = go rs
        tryMatches (m:ms) =
          case applyMatchWithMapper tt spliceMapper r m diag of
            Left _ -> tryMatches ms
            Right d ->
              pure (Just d)

rewriteOnceNestedRaw :: TypeTheory -> SpliceMapper -> [RewriteRule] -> Diagram -> Either Text (Maybe Diagram)
rewriteOnceNestedRaw tt spliceMapper rules diag =
  go (IM.toAscList (dEdges diag))
  where
    go [] = Right Nothing
    go ((edgeKey, edge):rest) =
      case ePayload edge of
        PSplice _ _ -> Left "rewriteOnce: splice nodes are not allowed in evaluation terms"
        PBox name inner -> do
          innerRes <- rewriteOnceRawWithMapper tt spliceMapper rules inner
          case innerRes of
            Nothing -> go rest
            Just inner' -> do
              let edge' = edge { ePayload = PBox name inner' }
              let diag' = diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
              pure (Just diag')
        PFeedback inner -> do
          innerRes <- rewriteOnceRawWithMapper tt spliceMapper rules inner
          case innerRes of
            Nothing -> go rest
            Just inner' -> do
              let edge' = edge { ePayload = PFeedback inner' }
              let diag' = diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
              pure (Just diag')
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
              pure (Just diag')
            Nothing -> do
              bargRes <- rewriteOnceBinderArgs bargs
              case bargRes of
                Nothing -> go rest
                Just bargs' -> do
                  let edge' = edge { ePayload = PGen gen args bargs' }
                  let diag' = diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
                  pure (Just diag')

    rewriteOnceCodeArgs [] = Right Nothing
    rewriteOnceCodeArgs (arg:args) =
      case arg of
        CAObj _ -> fmap (fmap (arg :)) (rewriteOnceCodeArgs args)
        CATm (TermDiagram inner) -> do
          res <- rewriteOnceRawWithMapper tt spliceMapper rules inner
          case res of
            Just inner' -> Right (Just (CATm (TermDiagram inner') : args))
            Nothing -> fmap (fmap (arg :)) (rewriteOnceCodeArgs args)

    rewriteOnceBinderArgs [] = Right Nothing
    rewriteOnceBinderArgs (b:bs) =
      case b of
        BAMeta _ -> fmap (fmap (b :)) (rewriteOnceBinderArgs bs)
        BAConcrete inner -> do
          res <- rewriteOnceRawWithMapper tt spliceMapper rules inner
          case res of
            Just inner' -> Right (Just (BAConcrete inner' : bs))
            Nothing -> fmap (fmap (b :)) (rewriteOnceBinderArgs bs)

rewriteAllWithMapper :: TypeTheory -> SpliceMapper -> Int -> [RewriteRule] -> Diagram -> Either Text [Diagram]
rewriteAllWithMapper tt spliceMapper cap rules diag = do
  rejectSplice "rewriteAll" diag
  top <- rewriteAllTop tt spliceMapper rules diag
  inner <- rewriteAllNested tt spliceMapper cap rules diag
  pure (take cap (top <> inner))
  where
    rewriteAllTop tt' spliceMapper' rules' diag' = go [] rules'
      where
        go acc [] = Right acc
        go acc (r:rs) = do
          if dMode (rrLHS r) /= dMode diag'
            then go acc rs
            else do
              matches <- findAllMatches (mkMatchConfig tt' r) (rrLHS r) diag'
              applied <- foldl collect (Right []) matches
              go (acc <> applied) rs
          where
            collect acc m =
              case acc of
                Left err -> Left err
                Right ds ->
                  case applyMatchWithMapper tt' spliceMapper' r m diag' of
                    Left _ -> Right ds
                    Right d -> Right (ds <> [d])

rewriteAll :: TypeTheory -> Int -> [RewriteRule] -> Diagram -> Either Text [Diagram]
rewriteAll tt =
  rewriteAllWithMapper tt defaultSpliceMapper

rewriteAllNested :: TypeTheory -> SpliceMapper -> Int -> [RewriteRule] -> Diagram -> Either Text [Diagram]
rewriteAllNested tt spliceMapper cap rules diag = do
  let edges = IM.toAscList (dEdges diag)
  fmap concat (mapM (rewriteInEdge tt spliceMapper cap rules diag) edges)

rewriteInEdge :: TypeTheory -> SpliceMapper -> Int -> [RewriteRule] -> Diagram -> (Int, Edge) -> Either Text [Diagram]
rewriteInEdge tt spliceMapper cap rules diag (edgeKey, edge) =
  case ePayload edge of
    PSplice _ _ -> Left "rewriteAll: splice nodes are not allowed in evaluation terms"
    PBox name inner -> do
      innerRes <- rewriteAllWithMapper tt spliceMapper cap rules inner
      mapM
        (\d ->
          let edge' = edge { ePayload = PBox name d }
              diag' = diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
           in Right diag')
        innerRes
    PFeedback inner -> do
      innerRes <- rewriteAllWithMapper tt spliceMapper cap rules inner
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
      argsRes <- rewriteAllCodeArgs tt spliceMapper cap rules args
      fromArgs <-
        mapM
          (\args' ->
            let edge' = edge { ePayload = PGen gen args' bargs }
                diag' = diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
             in Right diag')
          argsRes
      bargsRes <- rewriteAllBinderArgs tt spliceMapper cap rules bargs
      fromBinders <-
        mapM
          (\bargs' ->
            let edge' = edge { ePayload = PGen gen args bargs' }
                diag' = diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
             in Right diag')
          bargsRes
      pure (fromArgs <> fromBinders)

rewriteAllCodeArgs :: TypeTheory -> SpliceMapper -> Int -> [RewriteRule] -> [CodeArg] -> Either Text [[CodeArg]]
rewriteAllCodeArgs _ _ _ _ [] = Right []
rewriteAllCodeArgs tt spliceMapper cap rules args =
  fmap concat (mapM rewriteAt [0 .. length args - 1])
  where
    rewriteAt i =
      case splitAt i args of
        (pre, CATm (TermDiagram inner) : post) -> do
          res <- rewriteAllWithMapper tt spliceMapper cap rules inner
          pure [pre <> [CATm (TermDiagram inner')] <> post | inner' <- res]
        _ -> Right []

rewriteAllBinderArgs :: TypeTheory -> SpliceMapper -> Int -> [RewriteRule] -> [BinderArg] -> Either Text [[BinderArg]]
rewriteAllBinderArgs _ _ _ _ [] = Right []
rewriteAllBinderArgs tt spliceMapper cap rules args =
  fmap concat (mapM rewriteAt [0 .. length args - 1])
  where
    rewriteAt i =
      case splitAt i args of
        (pre, BAConcrete inner : post) -> do
          res <- rewriteAllWithMapper tt spliceMapper cap rules inner
          pure [pre <> [BAConcrete inner'] <> post | inner' <- res]
        _ -> Right []

applyMatchWithMapper :: TypeTheory -> SpliceMapper -> RewriteRule -> Match -> Diagram -> Either Text Diagram
applyMatchWithMapper tt spliceMapper rule match host = do
  rejectSplice "rewrite host" host
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
      validateDiagram host4
      pure host4
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

instantiateBinderMetas :: M.Map BinderMetaVar Diagram -> Diagram -> Either Text Diagram
instantiateBinderMetas binderSub =
  traverseDiagram pure pure pure onBinderArg
  where
    onBinderArg barg =
      case barg of
        BAConcrete inner -> Right (BAConcrete inner)
        BAMeta x ->
          case M.lookup x binderSub of
            Nothing -> Left "rewriteOnce: RHS uses uncaptured binder meta"
            Just captured -> Right (BAConcrete captured)

expandSplices :: SpliceMapper -> M.Map BinderMetaVar Diagram -> Diagram -> Either Text Diagram
expandSplices spliceMapper binderSub =
  traverseDiagram expandTop pure pure pure
  where
    expandTop diag =
      case findSpliceEdge diag of
        Nothing -> Right diag
        Just (edgeKey, edge, x, me) -> do
          captured <-
            case M.lookup x binderSub of
              Nothing -> Left "rewriteOnce: splice uses uncaptured binder meta"
              Just d -> Right d
          if dMode captured == meSrc me
            then Right ()
            else Left "rewriteOnce: splice mapper source-mode mismatch"
          capturedMapped <-
            if null (mePath me)
              then Right captured
              else spliceMapper me captured
          if dMode capturedMapped == meTgt me
            then Right ()
            else Left "rewriteOnce: splice mapper target-mode mismatch"
          if dTmCtx capturedMapped /= dTmCtx diag
            then Left "rewriteOnce: splice term-context mismatch"
            else Right ()
          domSplice <- mapM (requirePortType "rewriteOnce" diag) (eIns edge)
          codSplice <- mapM (requirePortType "rewriteOnce" diag) (eOuts edge)
          domCaptured <- mapM (requirePortType "rewriteOnce" capturedMapped) (dIn capturedMapped)
          codCaptured <- mapM (requirePortType "rewriteOnce" capturedMapped) (dOut capturedMapped)
          if domSplice /= domCaptured || codSplice /= codCaptured
            then Left "rewriteOnce: splice boundary mismatch"
            else Right ()
          diagMerged <- spliceEdge diag edgeKey capturedMapped
          expandTop diagMerged

findSpliceEdge :: Diagram -> Maybe (Int, Edge, BinderMetaVar, ModExpr)
findSpliceEdge diag =
  case
    [ (k, edge, x, me)
    | (k, edge) <- IM.toAscList (dEdges diag)
    , PSplice x me <- [ePayload edge]
    ]
    of
      [] -> Nothing
      (x:_) -> Just x

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

mkMatchConfig :: TypeTheory -> RewriteRule -> MatchConfig
mkMatchConfig tt rule =
  MatchConfig
    { mcTheory = tt
    , mcFlex = S.union (S.fromList (rrTyVars rule)) (S.fromList (rrTmVars rule))
    }
