{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Normalize
  ( NormalizationStatus(..)
  , normalizeWithMapper
  , normalize
  , autoJoinProofWithMapper
  , autoJoinProof
  ) where

import Data.Text (Text)
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.Diagram (Diagram(..))
import Strat.Poly.DefEq (defEqObjWithMapper)
import Strat.Poly.Graph
  ( CanonDiagram(..)
  , Edge(..)
  , EdgeId(..)
  , EdgePayload(..)
  , BinderArg(..)
  , canonDiagram
  )
import Strat.Poly.Obj (TermDiagram(..))
import Strat.Poly.Match (Match(..), buildHostIndex, findAllMatchesWithIndex, findAllMatchesWithIndexSeeded)
import Strat.Poly.Proof
  ( JoinProof(..)
  , RewritePath(..)
  , RewriteStep(..)
  , RewriteFocus(..)
  , RuleDir(..)
  , SearchLimit(..)
  , SearchOutcome(..)
  , SearchBudget(..)
  , checkJoinProofWithMapper
  )
import Strat.Poly.Rewrite
  ( RewriteRule
  , SpliceMapper
  , defaultSpliceMapper
  , rrLHS
  , rrName
  , applyMatchWithMapper
  , mkMatchConfig
  , rewriteOnceRawWithMapper
  )
import Strat.Poly.Syntax (CodeArg(..))
import Strat.Poly.TypeTheory (TypeTheory)


data NormalizationStatus a
  = Finished a
  | OutOfFuel a
  deriving (Eq, Show)

normalizeWithMapper :: SpliceMapper -> TypeTheory -> Int -> [RewriteRule] -> Diagram -> Either Text (NormalizationStatus Diagram)
normalizeWithMapper spliceMapper tt fuel rules diag =
  go fuel diag (allEdgeIds diag)
  where
    objEq = defEqObjWithMapper tt spliceMapper

    go remaining current worklist
      | remaining <= 0 =
          Right (OutOfFuel current)
      | otherwise = do
          localStep <- rewriteOnceTopWithCandidates current worklist
          step <-
            case localStep of
              Just (next, nextWorklist) ->
                Right (Just (next, nextWorklist))
              Nothing -> do
                fullStep <- rewriteOnceRawWithMapper objEq tt spliceMapper rules current
                case fullStep of
                  Nothing -> Right Nothing
                  Just next -> Right (Just (next, allEdgeIds next))
          case step of
            Nothing ->
              Right (Finished current)
            Just (next, nextWorklist) ->
              go (remaining - 1) next nextWorklist

    rewriteOnceTopWithCandidates current candidateEdges
      | S.null candidateEdges = Right Nothing
      | otherwise =
          let hostIndex = buildHostIndex current
           in goRules hostIndex rules
      where
        goRules _ [] = Right Nothing
        goRules hostIndex (rule:rest)
          | dMode (rrLHS rule) /= dMode current = goRules hostIndex rest
          | otherwise = do
              matches <- findAllMatchesWithIndexSeeded (mkMatchConfig objEq tt rule) (rrLHS rule) hostIndex candidateEdges current
              tryMatches rule matches
          where
            tryMatches _ [] = goRules hostIndex rest
            tryMatches rule (match:more) =
              case applyMatchWithMapper tt spliceMapper rule match current of
                Left _ -> tryMatches rule more
                Right next ->
                  Right (Just (next, affectedEdges current next match))

    affectedEdges before after match =
      let oldKeys = S.fromList (IM.keys (dEdges before))
          newKeys = S.fromList (IM.keys (dEdges after))
          inserted = S.map EdgeId (S.difference newKeys oldKeys)
          touchedPorts = S.fromList (M.elems (mPortMap match))
          adjacent = incidentEdges after touchedPorts
       in inserted `S.union` adjacent

    incidentEdges current ports =
      S.fromList
        [ eId edge
        | edge <- IM.elems (dEdges current)
        , any (`S.member` ports) (eIns edge <> eOuts edge)
        ]

    allEdgeIds current =
      S.fromList [eId edge | edge <- IM.elems (dEdges current)]

normalize :: TypeTheory -> Int -> [RewriteRule] -> Diagram -> Either Text (NormalizationStatus Diagram)
normalize = normalizeWithMapper defaultSpliceMapper

autoJoinProofWithMapper :: SpliceMapper -> TypeTheory -> SearchBudget -> [RewriteRule] -> Diagram -> Diagram -> Either Text (SearchOutcome JoinProof)
autoJoinProofWithMapper spliceMapper tt budget rules d1 d2
  | sbMaxDepth budget < 0 = Right (SearchUndecided LimitDepth)
  | sbMaxStates budget <= 0 = Right (SearchUndecided LimitStates)
  | sbTimeoutMs budget < 0 = Right (SearchUndecided LimitTimeout)
  | otherwise = do
      let cap = max 1 (min 100 (sbMaxStates budget))
      reach1 <- reachableWithParents spliceMapper tt rules budget cap d1
      reach2 <- reachableWithParents spliceMapper tt rules budget cap d2
      let nodes1 = rrNodes reach1
      let nodes2 = rrNodes reach2
      meet <- findMeet nodes1 nodes2
      case meet of
        Nothing -> Right (SearchUndecided (combineLimits (rrStop reach1) (rrStop reach2)))
        Just (i1, i2) -> do
          let leftPath = pathFrom nodes1 i1
          let rightPath = pathFrom nodes2 i2
          let proof = JoinProof { jpLeft = leftPath, jpRight = rightPath }
          checkJoinProofWithMapper spliceMapper tt rules proof
          Right (SearchProved proof)

autoJoinProof :: TypeTheory -> SearchBudget -> [RewriteRule] -> Diagram -> Diagram -> Either Text (SearchOutcome JoinProof)
autoJoinProof = autoJoinProofWithMapper defaultSpliceMapper

data Node = Node
  { nodeCanon :: CanonDiagram
  , nodeParent :: Maybe Int
  , nodeStep :: Maybe RewriteStep
  , nodeDepth :: Int
  } deriving (Eq, Show)

data ReachStop
  = ReachComplete
  | ReachDepthLimit
  | ReachStateLimit
  | ReachTimeoutLimit
  deriving (Eq, Show)

data ReachResult = ReachResult
  { rrNodes :: [Node]
  , rrStop :: ReachStop
  } deriving (Eq, Show)

nodeDiag :: Node -> Diagram
nodeDiag = unCanon . nodeCanon

reachableWithParents :: SpliceMapper -> TypeTheory -> [RewriteRule] -> SearchBudget -> Int -> Diagram -> Either Text ReachResult
reachableWithParents spliceMapper tt rules budget cap start = do
  startCanon <- canonDiagram start
  let startNode = Node startCanon Nothing Nothing 0
  go [startNode] (M.singleton startCanon 0) [0] False
  where
    go nodes _ [] hitDepth =
      Right
        ReachResult
          { rrNodes = nodes
          , rrStop = if hitDepth then ReachDepthLimit else ReachComplete
          }
    go nodes _ _ _
      | length nodes >= sbMaxStates budget =
          Right ReachResult { rrNodes = nodes, rrStop = ReachStateLimit }
    go nodes seen (idx:rest) hitDepth =
      case indexMaybe nodes idx of
        Nothing ->
          go nodes seen rest hitDepth
        Just node ->
          if nodeDepth node >= sbMaxDepth budget
            then go nodes seen rest True
            else do
              next0 <- rewriteAllWithProof spliceMapper tt cap rules (nodeDiag node)
              next <- mapM canonPair next0
              (nodes', seen', newIdxs) <- foldl (insertIfNew idx (nodeDepth node + 1)) (Right (nodes, seen, [])) next
              go nodes' seen' (rest <> newIdxs) hitDepth

    canonPair (step, diag) = do
      canon <- canonDiagram diag
      Right (step, canon)

    insertIfNew parent depth acc (step, canon) = do
      (nodes, seen, newIdxs) <- acc
      case M.lookup canon seen of
        Just _ ->
          Right (nodes, seen, newIdxs)
        Nothing -> do
          let idx = length nodes
          let node = Node canon (Just parent) (Just step) depth
          Right (nodes <> [node], M.insert canon idx seen, newIdxs <> [idx])

pathFrom :: [Node] -> Int -> RewritePath
pathFrom nodes idx =
  let chain = collect idx []
      startDiag =
        case (chain, nodes) of
          (r:_, _) -> nodeDiag (nodes !! r)
          ([], n:_) -> nodeDiag n
          ([], []) -> error "pathFrom: empty node set"
      steps =
        [ step
        | i <- drop 1 chain
        , Just step <- [nodeStep (nodes !! i)]
        ]
   in RewritePath { rpStart = startDiag, rpSteps = steps }
  where
    collect i acc =
      case indexMaybe nodes i of
        Nothing -> acc
        Just node ->
          let acc' = i : acc
           in case nodeParent node of
                Nothing -> acc'
                Just p -> collect p acc'

findMeet :: [Node] -> [Node] -> Either Text (Maybe (Int, Int))
findMeet nodes1 nodes2 = go 0
  where
    ix2 = M.fromList [ (nodeCanon n, i) | (i, n) <- zip [0 :: Int ..] nodes2 ]

    go i =
          if i >= length nodes1
            then Right Nothing
            else
              case M.lookup (nodeCanon (nodes1 !! i)) ix2 of
                Nothing -> go (i + 1)
                Just j -> Right (Just (i, j))

rewriteAllWithProof :: SpliceMapper -> TypeTheory -> Int -> [RewriteRule] -> Diagram -> Either Text [(RewriteStep, Diagram)]
rewriteAllWithProof spliceMapper tt cap rules diag = do
  top <- rewriteAllTopWithProof spliceMapper tt rules diag
  inner <- rewriteAllNestedWithProof spliceMapper tt cap rules diag
  pure (take cap (top <> inner))

rewriteAllTopWithProof :: SpliceMapper -> TypeTheory -> [RewriteRule] -> Diagram -> Either Text [(RewriteStep, Diagram)]
rewriteAllTopWithProof spliceMapper tt rules diag =
  let hostIndex = buildHostIndex diag
   in foldl (collect hostIndex) (Right []) (zip [0 :: Int ..] rules)
  where
    objEq = defEqObjWithMapper tt spliceMapper

    collect hostIndex acc (ruleIndex, rule) = do
      out <- acc
      if dMode (rrLHS rule) /= dMode diag
        then Right out
        else do
          matches <- findAllMatchesWithIndex (mkMatchConfig objEq tt rule) (rrLHS rule) hostIndex diag
          steps <- fmap concat (mapM (applyOne ruleIndex rule) matches)
          Right (out <> steps)

    applyOne ruleIndex rule match =
      case applyMatchWithMapper tt spliceMapper rule match diag of
        Left _ -> Right []
        Right d -> do
          let step =
                RewriteStep
                  { rsRuleName = rrName rule
                  , rsRuleIndex = ruleIndex
                  , rsDir = RuleLR
                  , rsMatch = match
                  , rsFocus = FocusTop
                  }
          Right [(step, d)]

rewriteAllNestedWithProof :: SpliceMapper -> TypeTheory -> Int -> [RewriteRule] -> Diagram -> Either Text [(RewriteStep, Diagram)]
rewriteAllNestedWithProof spliceMapper tt cap rules diag = do
  let edges = IM.toAscList (dEdges diag)
  fmap concat (mapM (rewriteInEdge spliceMapper tt cap rules diag) edges)

rewriteInEdge :: SpliceMapper -> TypeTheory -> Int -> [RewriteRule] -> Diagram -> (Int, Edge) -> Either Text [(RewriteStep, Diagram)]
rewriteInEdge spliceMapper tt cap rules diag (edgeKey, edge) =
  case ePayload edge of
    PSplice _ _ -> Right []
    PProvider _ -> Right []
    PModuleRef _ -> Right []
    PBox name inner -> do
      innerRes <- rewriteAllWithProof spliceMapper tt cap rules inner
      mapM (replaceBox name) innerRes
    PFeedback inner -> do
      innerRes <- rewriteAllWithProof spliceMapper tt cap rules inner
      mapM replaceFeedback innerRes
    PTmMeta _ ->
      Right []
    PTmLit _ ->
      Right []
    PInternalDrop ->
      Right []
    PGen gen args bargs -> do
      argRes <- rewriteAllCodeArgsWithProof spliceMapper tt cap rules args
      fromArgs <- mapM (replaceGenArg gen bargs) argRes
      bargsRes <- rewriteAllBinderArgsWithProof spliceMapper tt cap rules bargs
      fromBinders <- mapM (replaceGen gen args) bargsRes
      pure (fromArgs <> fromBinders)
  where
    prefix focus step = step { rsFocus = focus (rsFocus step) }

    replaceBox name (step, inner') = do
      let edge' = edge { ePayload = PBox name inner' }
      let diag' = diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
      Right (prefix (FocusInBox edgeKey) step, diag')

    replaceFeedback (step, inner') = do
      let edge' = edge { ePayload = PFeedback inner' }
      let diag' = diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
      Right (prefix (FocusInFeedback edgeKey) step, diag')

    replaceGenArg gen bargs (argIx, step, args') = do
      let edge' = edge { ePayload = PGen gen args' bargs }
      let diag' = diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
      Right (prefix (FocusInGenArg edgeKey argIx) step, diag')

    replaceGen gen args (binderIx, step, bargs') = do
      let edge' = edge { ePayload = PGen gen args bargs' }
      let diag' = diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
      Right (prefix (FocusInBinder edgeKey binderIx) step, diag')

rewriteAllCodeArgsWithProof :: SpliceMapper -> TypeTheory -> Int -> [RewriteRule] -> [CodeArg] -> Either Text [(Int, RewriteStep, [CodeArg])]
rewriteAllCodeArgsWithProof _ _ _ _ [] = Right []
rewriteAllCodeArgsWithProof spliceMapper tt cap rules args =
  fmap concat (mapM rewriteAt [0 .. length args - 1])
  where
    rewriteAt i =
      case splitAt i args of
        (pre, CATm (TermDiagram inner) : post) -> do
          res <- rewriteAllWithProof spliceMapper tt cap rules inner
          Right
            [ (i, step, pre <> [CATm (TermDiagram inner')] <> post)
            | (step, inner') <- res
            ]
        _ -> Right []

rewriteAllBinderArgsWithProof :: SpliceMapper -> TypeTheory -> Int -> [RewriteRule] -> [BinderArg] -> Either Text [(Int, RewriteStep, [BinderArg])]
rewriteAllBinderArgsWithProof _ _ _ _ [] = Right []
rewriteAllBinderArgsWithProof spliceMapper tt cap rules args =
  fmap concat (mapM rewriteAt [0 .. length args - 1])
  where
    rewriteAt i =
      case splitAt i args of
        (pre, BAConcrete inner : post) -> do
          res <- rewriteAllWithProof spliceMapper tt cap rules inner
          Right
            [ (i, step, pre <> [BAConcrete inner'] <> post)
            | (step, inner') <- res
            ]
        _ -> Right []

combineLimits :: ReachStop -> ReachStop -> SearchLimit
combineLimits s1 s2
  | any (== ReachTimeoutLimit) [s1, s2] = LimitTimeout
  | any (== ReachStateLimit) [s1, s2] = LimitStates
  | any (== ReachDepthLimit) [s1, s2] = LimitDepth
  | otherwise = LimitExhausted

indexMaybe :: [a] -> Int -> Maybe a
indexMaybe xs i
  | i < 0 = Nothing
  | otherwise =
      case drop i xs of
        (y:_) -> Just y
        [] -> Nothing
