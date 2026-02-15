{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Rewrite
  ( RewriteRule(..)
  , rewriteOnce
  , rewriteAll
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
import Strat.Poly.Diagram
import Strat.Poly.Match
import Strat.Poly.TypeExpr (TyVar, TmVar, TypeExpr)
import Strat.Poly.Cell2
import Strat.Poly.UnifyTy (emptySubst)
import Strat.Common.Rules (RewritePolicy(..))
import Strat.Common.Rules (Orientation(..), RuleClass(..))
import Strat.Poly.TypeTheory (TypeTheory)
import Strat.Poly.Traversal (foldDiagram, traverseDiagram)


data RewriteRule = RewriteRule
  { rrName   :: Text
  , rrLHS    :: Diagram
  , rrRHS    :: Diagram
  , rrTyVars :: [TyVar]
  , rrTmVars :: [TmVar]
  } deriving (Eq, Show)

rewriteOnce :: TypeTheory -> [RewriteRule] -> Diagram -> Either Text (Maybe Diagram)
rewriteOnce tt rules diag = do
  rejectSplice "rewriteOnce" diag
  top <- rewriteOnceTop tt rules diag
  case top of
    Just _ -> pure top
    Nothing -> rewriteOnceNested tt rules diag

rewriteOnceTop :: TypeTheory -> [RewriteRule] -> Diagram -> Either Text (Maybe Diagram)
rewriteOnceTop tt rules diag = go rules
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
          case applyMatch tt r m diag of
            Left _ -> tryMatches ms
            Right d -> do
              canon <- canonDiagramRaw d
              pure (Just canon)

rewriteOnceNested :: TypeTheory -> [RewriteRule] -> Diagram -> Either Text (Maybe Diagram)
rewriteOnceNested tt rules diag =
  go (IM.toAscList (dEdges diag))
  where
    go [] = Right Nothing
    go ((edgeKey, edge):rest) =
      case ePayload edge of
        PSplice _ -> Left "rewriteOnce: splice nodes are not allowed in evaluation terms"
        PBox name inner -> do
          innerRes <- rewriteOnce tt rules inner
          case innerRes of
            Nothing -> go rest
            Just inner' -> do
              let edge' = edge { ePayload = PBox name inner' }
              let diag' = diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
              canon <- canonDiagramRaw diag'
              pure (Just canon)
        PFeedback inner -> do
          innerRes <- rewriteOnce tt rules inner
          case innerRes of
            Nothing -> go rest
            Just inner' -> do
              let edge' = edge { ePayload = PFeedback inner' }
              let diag' = diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
              canon <- canonDiagramRaw diag'
              pure (Just canon)
        PTmMeta _ ->
          go rest
        PInternalDrop ->
          go rest
        PGen gen attrs bargs -> do
          bargRes <- rewriteOnceBinderArgs bargs
          case bargRes of
            Nothing -> go rest
            Just bargs' -> do
              let edge' = edge { ePayload = PGen gen attrs bargs' }
              let diag' = diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
              canon <- canonDiagramRaw diag'
              pure (Just canon)

    rewriteOnceBinderArgs [] = Right Nothing
    rewriteOnceBinderArgs (b:bs) =
      case b of
        BAMeta _ -> rewriteOnceBinderArgs bs
        BAConcrete inner -> do
          res <- rewriteOnce tt rules inner
          case res of
            Just inner' -> Right (Just (BAConcrete inner' : bs))
            Nothing -> do
              rest <- rewriteOnceBinderArgs bs
              pure (fmap (b :) rest)

rewriteAll :: TypeTheory -> Int -> [RewriteRule] -> Diagram -> Either Text [Diagram]
rewriteAll tt cap rules diag = do
  rejectSplice "rewriteAll" diag
  top <- rewriteAllTop tt rules diag
  inner <- rewriteAllNested tt cap rules diag
  pure (take cap (top <> inner))
  where
    rewriteAllTop tt' rules' diag' = go [] rules'
      where
        go acc [] = Right acc
        go acc (r:rs) = do
          if dMode (rrLHS r) /= dMode diag'
            then go acc rs
            else do
              matches <- findAllMatches (mkMatchConfig tt' r) (rrLHS r) diag'
              applied <- foldl collect (Right []) matches
              canon <- mapM canonDiagramRaw applied
              go (acc <> canon) rs
          where
            collect acc m =
              case acc of
                Left err -> Left err
                Right ds ->
                  case applyMatch tt' r m diag' of
                    Left _ -> Right ds
                    Right d -> Right (ds <> [d])

rewriteAllNested :: TypeTheory -> Int -> [RewriteRule] -> Diagram -> Either Text [Diagram]
rewriteAllNested tt cap rules diag = do
  let edges = IM.toAscList (dEdges diag)
  fmap concat (mapM (rewriteInEdge tt cap rules diag) edges)

rewriteInEdge :: TypeTheory -> Int -> [RewriteRule] -> Diagram -> (Int, Edge) -> Either Text [Diagram]
rewriteInEdge tt cap rules diag (edgeKey, edge) =
  case ePayload edge of
    PSplice _ -> Left "rewriteAll: splice nodes are not allowed in evaluation terms"
    PBox name inner -> do
      innerRes <- rewriteAll tt cap rules inner
      mapM
        (\d -> do
          let edge' = edge { ePayload = PBox name d }
          let diag' = diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
          canonDiagramRaw diag')
        innerRes
    PFeedback inner -> do
      innerRes <- rewriteAll tt cap rules inner
      mapM
        (\d -> do
          let edge' = edge { ePayload = PFeedback d }
          let diag' = diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
          canonDiagramRaw diag')
        innerRes
    PTmMeta _ ->
      Right []
    PInternalDrop ->
      Right []
    PGen gen attrs bargs -> do
      bargsRes <- rewriteAllBinderArgs tt cap rules bargs
      mapM
        (\bargs' -> do
          let edge' = edge { ePayload = PGen gen attrs bargs' }
          let diag' = diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
          canonDiagramRaw diag')
        bargsRes

rewriteAllBinderArgs :: TypeTheory -> Int -> [RewriteRule] -> [BinderArg] -> Either Text [[BinderArg]]
rewriteAllBinderArgs _ _ _ [] = Right []
rewriteAllBinderArgs tt cap rules args =
  fmap concat (mapM rewriteAt [0 .. length args - 1])
  where
    rewriteAt i =
      case splitAt i args of
        (pre, BAConcrete inner : post) -> do
          res <- rewriteAll tt cap rules inner
          pure [pre <> [BAConcrete inner'] <> post | inner' <- res]
        _ -> Right []

applyMatch :: TypeTheory -> RewriteRule -> Match -> Diagram -> Either Text Diagram
applyMatch tt rule match host = do
  rejectSplice "rewrite host" host
  -- Normalize host boundary types before gluing so mergePorts compares
  -- canonicalized types (e.g. after modality/term equations).
  hostNorm <- applySubstDiagram tt emptySubst host
  let lhs = rrLHS rule
  rhsSub <- applySubstDiagram tt (mTySubst match) (rrRHS rule)
  let rhs0 = applyAttrSubstDiagram (mAttrSubst match) rhsSub
  rhs1 <- instantiateBinderMetas (mBinderSub match) rhs0
  rhs <- expandSplices (mBinderSub match) rhs1
  host1 <- deleteMatchedEdges hostNorm (M.elems (mEdgeMap match))
  host2 <- deleteMatchedPorts host1 (internalPorts lhs) (mPortMap match)
  let rhsShift = shiftDiagram (dNextPort host2) (dNextEdge host2) rhs
  host3 <- unionDiagram host2 rhsShift
  let lhsBoundary = dIn lhs <> dOut lhs
  let rhsBoundary = dIn rhsShift <> dOut rhsShift
  if length lhsBoundary /= length rhsBoundary
    then Left "rewriteOnce: boundary length mismatch"
    else do
      boundaryPairs <- mapM toBoundaryPair (zip lhsBoundary rhsBoundary)
      host4 <- mergeBoundaryPairs host3 boundaryPairs
      validateDiagram host4
      pure host4
  where
    toBoundaryPair (lhsPort, rhsPort) =
      case M.lookup lhsPort (mPortMap match) of
        Nothing -> Left "rewriteOnce: missing boundary port mapping"
        Just hostPort -> Right (hostPort, rhsPort)

instantiateBinderMetas :: M.Map BinderMetaVar Diagram -> Diagram -> Either Text Diagram
instantiateBinderMetas binderSub =
  traverseDiagram pure pure onBinderArg
  where
    onBinderArg barg =
      case barg of
        BAConcrete inner -> Right (BAConcrete inner)
        BAMeta x ->
          case M.lookup x binderSub of
            Nothing -> Left "rewriteOnce: RHS uses uncaptured binder meta"
            Just captured -> Right (BAConcrete captured)

expandSplices :: M.Map BinderMetaVar Diagram -> Diagram -> Either Text Diagram
expandSplices binderSub =
  traverseDiagram expandTop pure pure
  where
    expandTop diag =
      case findSpliceEdge diag of
        Nothing -> Right diag
        Just (_, edge, x) -> do
          captured <-
            case M.lookup x binderSub of
              Nothing -> Left "rewriteOnce: splice uses uncaptured binder meta"
              Just d -> Right d
          if dTmCtx captured /= dTmCtx diag
            then Left "rewriteOnce: splice term-context mismatch"
            else Right ()
          domSplice <- mapM (requirePortType diag) (eIns edge)
          codSplice <- mapM (requirePortType diag) (eOuts edge)
          domCaptured <- mapM (requirePortType captured) (dIn captured)
          codCaptured <- mapM (requirePortType captured) (dOut captured)
          if domSplice /= domCaptured || codSplice /= codCaptured
            then Left "rewriteOnce: splice boundary mismatch"
            else Right ()
          diagNoEdge <- deleteEdgeKeepPorts diag (eId edge)
          let capturedShift = shiftDiagram (dNextPort diagNoEdge) (dNextEdge diagNoEdge) captured
          diagInserted <- unionDiagram diagNoEdge capturedShift
          let splicePairs = zip (eIns edge) (dIn capturedShift) <> zip (eOuts edge) (dOut capturedShift)
          diagMerged <- mergeBoundaryPairs diagInserted splicePairs
          validateDiagram diagMerged
          expandTop diagMerged

findSpliceEdge :: Diagram -> Maybe (Int, Edge, BinderMetaVar)
findSpliceEdge diag =
  case
    [ (k, edge, x)
    | (k, edge) <- IM.toAscList (dEdges diag)
    , PSplice x <- [ePayload edge]
    ]
    of
      [] -> Nothing
      (x:_) -> Just x

requirePortType :: Diagram -> PortId -> Either Text TypeExpr
requirePortType diag pid =
  case diagramPortType diag pid of
    Nothing -> Left "rewriteOnce: missing port type"
    Just ty -> Right ty

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
  getAny . foldDiagram (\_ -> mempty) onPayload (\_ -> mempty)
  where
    onPayload payload =
      Any $
        case payload of
          PSplice _ -> True
          _ -> False

mkMatchConfig :: TypeTheory -> RewriteRule -> MatchConfig
mkMatchConfig tt rule =
  MatchConfig
    { mcTheory = tt
    , mcTyFlex = S.fromList (rrTyVars rule)
    , mcTmFlex = S.fromList (rrTmVars rule)
    , mcAttrFlex = freeAttrVarsDiagram (rrLHS rule)
    }
