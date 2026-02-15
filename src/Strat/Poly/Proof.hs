{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Proof
  ( RuleDir(..)
  , RewriteFocus(..)
  , RewriteStep(..)
  , RewritePath(..)
  , JoinProof(..)
  , SearchLimit(..)
  , SearchOutcome(..)
  , SearchBudget(..)
  , defaultSearchBudget
  , renderSearchLimit
  , checkRewriteStep
  , checkRewritePath
  , checkJoinProof
  ) where

import Control.Monad (foldM)
import Data.Text (Text)
import qualified Data.IntMap.Strict as IM
import Strat.Poly.Diagram (Diagram(..))
import Strat.Poly.Graph (Edge(..), EdgePayload(..), BinderArg(..), canonDiagramRaw, diagramIsoEq)
import Strat.Poly.Match (Match, findAllMatches)
import Strat.Poly.Rewrite (RewriteRule(..), applyMatch, mkMatchConfig)
import Strat.Poly.TypeTheory (TypeTheory)


data RuleDir = RuleLR | RuleRL | RuleBi
  deriving (Eq, Ord, Show)

data RewriteFocus
  = FocusTop
  | FocusInBox Int RewriteFocus
  | FocusInFeedback Int RewriteFocus
  | FocusInBinder Int Int RewriteFocus
  deriving (Eq, Ord, Show)

data RewriteStep = RewriteStep
  { rsRuleName :: Text
  , rsRuleIndex :: Int
  , rsDir :: RuleDir
  , rsMatch :: Match
  , rsFocus :: RewriteFocus
  } deriving (Eq, Show)

data RewritePath = RewritePath
  { rpStart :: Diagram
  , rpSteps :: [RewriteStep]
  } deriving (Eq, Show)

data JoinProof = JoinProof
  { jpLeft :: RewritePath
  , jpRight :: RewritePath
  } deriving (Eq, Show)

data SearchLimit
  = LimitDepth
  | LimitStates
  | LimitTimeout
  | LimitExhausted
  deriving (Eq, Ord, Show)

data SearchOutcome a
  = SearchProved a
  | SearchUndecided SearchLimit
  deriving (Eq, Show)

data SearchBudget = SearchBudget
  { sbMaxDepth :: Int
  , sbMaxStates :: Int
  , sbTimeoutMs :: Int
  } deriving (Eq, Show)

defaultSearchBudget :: SearchBudget
defaultSearchBudget =
  SearchBudget
    { sbMaxDepth = 50
    , sbMaxStates = 10000
    , sbTimeoutMs = 0
    }

renderSearchLimit :: SearchLimit -> Text
renderSearchLimit lim =
  case lim of
    LimitDepth -> "depth budget exhausted"
    LimitStates -> "state budget exhausted"
    LimitTimeout -> "timeout budget exhausted"
    LimitExhausted -> "search exhausted without finding a join proof"

checkRewriteStep :: TypeTheory -> [RewriteRule] -> Diagram -> RewriteStep -> Either Text Diagram
checkRewriteStep tt rules current step = do
  baseRule <-
    case drop (rsRuleIndex step) rules of
      (r:_) -> Right r
      [] -> Left "checkRewriteStep: rule index out of bounds"
  if rrName baseRule == rsRuleName step
    then Right ()
    else Left "checkRewriteStep: rule name/index mismatch"
  candidates <- candidateRules baseRule (rsDir step)
  tryCandidates candidates
  where
    candidateRules rule dir =
      case dir of
        RuleLR -> Right [rule]
        RuleRL -> Right [flipRule rule]
        RuleBi -> Right [rule, flipRule rule]

    tryCandidates [] = Left "checkRewriteStep: step does not replay under any permitted orientation"
    tryCandidates (rule:rest) =
      case applyAtFocus tt (rsFocus step) (rsMatch step) current rule of
        Right out -> Right out
        Left _ -> tryCandidates rest

applyAtFocus
  :: TypeTheory
  -> RewriteFocus
  -> Match
  -> Diagram
  -> RewriteRule
  -> Either Text Diagram
applyAtFocus tt focus match diag rule =
  case focus of
    FocusTop -> applyTop tt match diag rule
    FocusInBox edgeKey innerFocus -> do
      edge <- requireEdge edgeKey diag
      case ePayload edge of
        PBox name inner -> do
          inner' <- applyAtFocus tt innerFocus match inner rule
          let edge' = edge { ePayload = PBox name inner' }
          canonDiagramRaw diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
        _ -> Left "checkRewriteStep: focus does not point to box payload"
    FocusInFeedback edgeKey innerFocus -> do
      edge <- requireEdge edgeKey diag
      case ePayload edge of
        PFeedback inner -> do
          inner' <- applyAtFocus tt innerFocus match inner rule
          let edge' = edge { ePayload = PFeedback inner' }
          canonDiagramRaw diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
        _ -> Left "checkRewriteStep: focus does not point to feedback payload"
    FocusInBinder edgeKey binderIx innerFocus -> do
      edge <- requireEdge edgeKey diag
      case ePayload edge of
        PGen g attrs bargs -> do
          barg <- requireBinderArg binderIx bargs
          case barg of
            BAConcrete inner -> do
              inner' <- applyAtFocus tt innerFocus match inner rule
              let bargs' = replaceAt binderIx (BAConcrete inner') bargs
              let edge' = edge { ePayload = PGen g attrs bargs' }
              canonDiagramRaw diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
            BAMeta _ ->
              Left "checkRewriteStep: focus points to binder meta argument"
        _ -> Left "checkRewriteStep: focus does not point to generator payload"

applyTop :: TypeTheory -> Match -> Diagram -> RewriteRule -> Either Text Diagram
applyTop tt match diag rule = do
  matches <- findAllMatches (mkMatchConfig tt rule) (rrLHS rule) diag
  if match `elem` matches
    then Right ()
    else Left "checkRewriteStep: stored match is not valid at focused diagram"
  out <- applyMatch tt rule match diag
  canonDiagramRaw out

checkRewritePath :: TypeTheory -> [RewriteRule] -> RewritePath -> Either Text Diagram
checkRewritePath tt rules path = do
  start <- canonDiagramRaw (rpStart path)
  foldM (checkRewriteStep tt rules) start (rpSteps path)

checkJoinProof :: TypeTheory -> [RewriteRule] -> JoinProof -> Either Text ()
checkJoinProof tt rules proof = do
  leftEnd <- checkRewritePath tt rules (jpLeft proof)
  rightEnd <- checkRewritePath tt rules (jpRight proof)
  ok <- diagramIsoEq leftEnd rightEnd
  if ok
    then Right ()
    else Left "checkJoinProof: endpoints are not isomorphic"

flipRule :: RewriteRule -> RewriteRule
flipRule rule =
  rule
    { rrLHS = rrRHS rule
    , rrRHS = rrLHS rule
    }

requireEdge :: Int -> Diagram -> Either Text Edge
requireEdge edgeKey diag =
  case IM.lookup edgeKey (dEdges diag) of
    Nothing -> Left "checkRewriteStep: focus edge missing"
    Just edge -> Right edge

requireBinderArg :: Int -> [BinderArg] -> Either Text BinderArg
requireBinderArg idx bargs
  | idx < 0 = Left "checkRewriteStep: binder index out of bounds"
  | otherwise =
      case drop idx bargs of
        (b:_) -> Right b
        [] -> Left "checkRewriteStep: binder index out of bounds"

replaceAt :: Int -> a -> [a] -> [a]
replaceAt idx x xs =
  case splitAt idx xs of
    (pre, _old:post) -> pre <> [x] <> post
    _ -> xs
