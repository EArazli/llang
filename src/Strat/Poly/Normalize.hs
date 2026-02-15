{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Normalize
  ( NormalizationStatus(..)
  , normalize
  , autoJoinProof
  ) where

import Data.Text (Text)
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import GHC.Clock (getMonotonicTimeNSec)
import System.IO.Unsafe (unsafePerformIO)
import Strat.Poly.Diagram (Diagram(..))
import Strat.Poly.Graph
  ( CanonDiagram(..)
  , Edge(..)
  , EdgePayload(..)
  , BinderArg(..)
  , canonDiagram
  , canonDiagramRaw
  )
import Strat.Poly.Match (findAllMatches)
import Strat.Poly.Proof
  ( JoinProof(..)
  , RewritePath(..)
  , RewriteStep(..)
  , RewriteFocus(..)
  , RuleDir(..)
  , SearchLimit(..)
  , SearchOutcome(..)
  , SearchBudget(..)
  , checkJoinProof
  )
import Strat.Poly.Rewrite (RewriteRule, rrLHS, rrName, applyMatch, mkMatchConfig, rewriteOnce)
import Strat.Poly.TypeTheory (TypeTheory)


data NormalizationStatus a
  = Finished a
  | OutOfFuel a
  deriving (Eq, Show)

normalize :: TypeTheory -> Int -> [RewriteRule] -> Diagram -> Either Text (NormalizationStatus Diagram)
normalize tt fuel rules diag = do
  start <- canonDiagramRaw diag
  go fuel start
  where
    go remaining current
      | remaining <= 0 =
          Right (OutOfFuel current)
      | otherwise = do
          step <- rewriteOnce tt rules current
          case step of
            Nothing ->
              Right (Finished current)
            Just next -> do
              nextCanon <- canonDiagramRaw next
              go (remaining - 1) nextCanon

autoJoinProof :: TypeTheory -> SearchBudget -> [RewriteRule] -> Diagram -> Diagram -> Either Text (SearchOutcome JoinProof)
autoJoinProof tt budget rules d1 d2
  | sbMaxDepth budget < 0 = Right (SearchUndecided LimitDepth)
  | sbMaxStates budget <= 0 = Right (SearchUndecided LimitStates)
  | sbTimeoutMs budget < 0 = Right (SearchUndecided LimitTimeout)
  | otherwise = do
      let cap = max 1 (min 100 (sbMaxStates budget))
      let deadlineNs = timeoutDeadlineNs (sbTimeoutMs budget)
      if timedOut deadlineNs 0
        then Right (SearchUndecided LimitTimeout)
        else do
          reach1 <- reachableWithParents tt rules budget deadlineNs cap d1
          reach2 <- reachableWithParents tt rules budget deadlineNs cap d2
          let nodes1 = rrNodes reach1
          let nodes2 = rrNodes reach2
          meet <- findMeet nodes1 nodes2
          case meet of
            Nothing -> Right (SearchUndecided (combineLimits (rrStop reach1) (rrStop reach2)))
            Just (i1, i2) -> do
              let leftPath = pathFrom nodes1 i1
              let rightPath = pathFrom nodes2 i2
              let proof = JoinProof { jpLeft = leftPath, jpRight = rightPath }
              checkJoinProof tt rules proof
              Right (SearchProved proof)

timeoutDeadlineNs :: Int -> Maybe Integer
timeoutDeadlineNs timeoutMs
  | timeoutMs <= 0 = Nothing
  | otherwise =
      let nowNs = monotonicNowNs timeoutMs
          spanNs = toInteger timeoutMs * 1000000
       in Just (nowNs + spanNs)

timedOut :: Maybe Integer -> Int -> Bool
timedOut mDeadline salt =
  case mDeadline of
    Nothing -> False
    Just deadlineNs -> monotonicNowNs salt >= deadlineNs

-- This keeps search APIs pure while enforcing real wall-clock timeout semantics.
-- The salt argument prevents accidental sharing/CSE of calls at optimization time.
monotonicNowNs :: Int -> Integer
monotonicNowNs !salt =
  let !_ = salt
   in unsafePerformIO (toInteger <$> getMonotonicTimeNSec)
{-# NOINLINE monotonicNowNs #-}

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

reachableWithParents :: TypeTheory -> [RewriteRule] -> SearchBudget -> Maybe Integer -> Int -> Diagram -> Either Text ReachResult
reachableWithParents tt rules budget deadlineNs cap start = do
  startCanon <- canonDiagram start
  let startNode = Node startCanon Nothing Nothing 0
  go [startNode] (M.singleton startCanon 0) [0] 0 False
  where
    go nodes _ [] _ hitDepth =
      Right
        ReachResult
          { rrNodes = nodes
          , rrStop = if hitDepth then ReachDepthLimit else ReachComplete
          }
    go nodes _ _ _ _
      | length nodes >= sbMaxStates budget =
          Right ReachResult { rrNodes = nodes, rrStop = ReachStateLimit }
    go nodes _ _ !ticks _
      | timedOut deadlineNs ticks =
          Right ReachResult { rrNodes = nodes, rrStop = ReachTimeoutLimit }
    go nodes seen (idx:rest) !ticks hitDepth =
      case indexMaybe nodes idx of
        Nothing ->
          go nodes seen rest (ticks + 1) hitDepth
        Just node ->
          if nodeDepth node >= sbMaxDepth budget
            then go nodes seen rest (ticks + 1) True
            else do
              next0 <- rewriteAllWithProof tt cap rules (nodeDiag node)
              next <- mapM canonPair next0
              (nodes', seen', newIdxs) <- foldl (insertIfNew idx (nodeDepth node + 1)) (Right (nodes, seen, [])) next
              go nodes' seen' (rest <> newIdxs) (ticks + 1) hitDepth

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

rewriteAllWithProof :: TypeTheory -> Int -> [RewriteRule] -> Diagram -> Either Text [(RewriteStep, Diagram)]
rewriteAllWithProof tt cap rules diag = do
  rejectSplice "rewriteAll" diag
  top <- rewriteAllTopWithProof tt rules diag
  inner <- rewriteAllNestedWithProof tt cap rules diag
  pure (take cap (top <> inner))

rewriteAllTopWithProof :: TypeTheory -> [RewriteRule] -> Diagram -> Either Text [(RewriteStep, Diagram)]
rewriteAllTopWithProof tt rules diag =
  foldl collect (Right []) (zip [0 :: Int ..] rules)
  where
    collect acc (ruleIndex, rule) = do
      out <- acc
      if dMode (rrLHS rule) /= dMode diag
        then Right out
        else do
          matches <- findAllMatches (mkMatchConfig tt rule) (rrLHS rule) diag
          steps <- fmap concat (mapM (applyOne ruleIndex rule) matches)
          Right (out <> steps)

    applyOne ruleIndex rule match =
      case applyMatch tt rule match diag of
        Left _ -> Right []
        Right d -> do
          canon <- canonDiagramRaw d
          let step =
                RewriteStep
                  { rsRuleName = rrName rule
                  , rsRuleIndex = ruleIndex
                  , rsDir = RuleLR
                  , rsMatch = match
                  , rsFocus = FocusTop
                  }
          Right [(step, canon)]

rewriteAllNestedWithProof :: TypeTheory -> Int -> [RewriteRule] -> Diagram -> Either Text [(RewriteStep, Diagram)]
rewriteAllNestedWithProof tt cap rules diag = do
  let edges = IM.toAscList (dEdges diag)
  fmap concat (mapM (rewriteInEdge tt cap rules diag) edges)

rewriteInEdge :: TypeTheory -> Int -> [RewriteRule] -> Diagram -> (Int, Edge) -> Either Text [(RewriteStep, Diagram)]
rewriteInEdge tt cap rules diag (edgeKey, edge) =
  case ePayload edge of
    PSplice _ -> Left "rewriteAll: splice nodes are not allowed in evaluation terms"
    PBox name inner -> do
      innerRes <- rewriteAllWithProof tt cap rules inner
      mapM (replaceBox name) innerRes
    PFeedback inner -> do
      innerRes <- rewriteAllWithProof tt cap rules inner
      mapM replaceFeedback innerRes
    PTmMeta _ ->
      Right []
    PInternalDrop ->
      Right []
    PGen gen attrs bargs -> do
      bargsRes <- rewriteAllBinderArgsWithProof tt cap rules bargs
      mapM (replaceGen gen attrs) bargsRes
  where
    prefix focus step = step { rsFocus = focus (rsFocus step) }

    replaceBox name (step, inner') = do
      let edge' = edge { ePayload = PBox name inner' }
      let diag' = diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
      canon <- canonDiagramRaw diag'
      Right (prefix (FocusInBox edgeKey) step, canon)

    replaceFeedback (step, inner') = do
      let edge' = edge { ePayload = PFeedback inner' }
      let diag' = diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
      canon <- canonDiagramRaw diag'
      Right (prefix (FocusInFeedback edgeKey) step, canon)

    replaceGen gen attrs (binderIx, step, bargs') = do
      let edge' = edge { ePayload = PGen gen attrs bargs' }
      let diag' = diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
      canon <- canonDiagramRaw diag'
      Right (prefix (FocusInBinder edgeKey binderIx) step, canon)

rewriteAllBinderArgsWithProof :: TypeTheory -> Int -> [RewriteRule] -> [BinderArg] -> Either Text [(Int, RewriteStep, [BinderArg])]
rewriteAllBinderArgsWithProof _ _ _ [] = Right []
rewriteAllBinderArgsWithProof tt cap rules args =
  fmap concat (mapM rewriteAt [0 .. length args - 1])
  where
    rewriteAt i =
      case splitAt i args of
        (pre, BAConcrete inner : post) -> do
          res <- rewriteAllWithProof tt cap rules inner
          Right
            [ (i, step, pre <> [BAConcrete inner'] <> post)
            | (step, inner') <- res
            ]
        _ -> Right []

rejectSplice :: Text -> Diagram -> Either Text ()
rejectSplice label diag =
  if hasSplice diag
    then Left (label <> ": splice nodes are not allowed in evaluation terms")
    else Right ()

hasSplice :: Diagram -> Bool
hasSplice diag = any edgeHasSplice (IM.elems (dEdges diag))
  where
    edgeHasSplice edge =
      case ePayload edge of
        PSplice _ -> True
        PBox _ inner -> hasSplice inner
        PFeedback inner -> hasSplice inner
        PGen _ _ bargs -> any bargHasSplice bargs
        _ -> False

    bargHasSplice barg =
      case barg of
        BAConcrete inner -> hasSplice inner
        BAMeta _ -> False

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
