{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Coherence
  ( ObligationKind(..)
  , Obligation(..)
  , ObligationResult(..)
  , checkCoherence
  , renderCoherenceReport
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.List as L
import qualified Data.IntMap.Strict as IM
import Strat.Poly.CriticalPairs
import Strat.Poly.Normalize (autoJoinProof)
import Strat.Poly.Rewrite (rulesFromPolicy, RewriteRule)
import Strat.Poly.Doctrine (Doctrine(..), doctrineTypeTheory)
import Strat.Poly.Proof (JoinProof, SearchBudget, SearchOutcome(..), renderSearchLimit)
import Strat.Poly.TypeTheory (TypeTheory)
import Strat.Common.Rules (RewritePolicy)
import Strat.Common.Rules (RuleClass(..))
import Strat.Poly.Pretty (renderDiagram)
import Strat.Poly.Graph (Diagram(..))


data ObligationKind = NeedsJoin | NeedsCommute
  deriving (Eq, Ord, Show)

data Obligation = Obligation
  { obKind :: ObligationKind
  , obCP   :: CriticalPair
  } deriving (Eq, Show)

data ObligationResult = ObligationResult
  { orObligation :: Obligation
  , orWitness :: SearchOutcome JoinProof
  } deriving (Eq, Show)

checkCoherence :: CPMode -> RewritePolicy -> SearchBudget -> Doctrine -> Either Text [ObligationResult]
checkCoherence mode policy budget doc = do
  cps <- criticalPairsForDoctrine mode policy doc
  tt <- doctrineTypeTheory doc
  let obligations = concatMap (obligationsFor mode) cps
  let rules = rulesFromPolicy policy (dCells2 doc)
  mapM (checkObligation tt budget rules) obligations

obligationsFor :: CPMode -> CriticalPairInfo -> [Obligation]
obligationsFor mode info =
  case (cpiClass1 info, cpiClass2 info) of
    (Structural, Structural) -> [Obligation NeedsCommute (cpiPair info)]
    (Structural, Computational) -> [Obligation NeedsJoin (cpiPair info)]
    (Computational, Structural) -> [Obligation NeedsJoin (cpiPair info)]
    (Computational, Computational) ->
      if mode == CP_All then [Obligation NeedsJoin (cpiPair info)] else []

checkObligation :: TypeTheory -> SearchBudget -> [RewriteRule] -> Obligation -> Either Text ObligationResult
checkObligation tt budget rules ob = do
  outcome <- autoJoinProof tt budget rules (cpLeft (obCP ob)) (cpRight (obCP ob))
  pure ObligationResult { orObligation = ob, orWitness = outcome }

renderCoherenceReport :: [ObligationResult] -> Either Text Text
renderCoherenceReport results = do
  let total = length results
  let joins = length [() | r <- results, obKind (orObligation r) == NeedsJoin]
  let commutes = length [() | r <- results, obKind (orObligation r) == NeedsCommute]
  let failures = [ r | r <- results, isUndecided r ]
  let failureCount = length failures
  let header =
        [ "coherence:"
        , "  obligations: " <> T.pack (show total)
        , "  join: " <> T.pack (show joins)
        , "  commute: " <> T.pack (show commutes)
        , "  failures: " <> T.pack (show failureCount)
        ]
  details <- renderFailures (take 5 (sortFailures failures))
  pure (T.intercalate "\n" (header <> details))

sortFailures :: [ObligationResult] -> [ObligationResult]
sortFailures =
  L.sortOn (\r -> IM.size (dEdges (cpOverlap (obCP (orObligation r)))))

isUndecided :: ObligationResult -> Bool
isUndecided result =
  case orWitness result of
    SearchProved _ -> False
    SearchUndecided _ -> True

renderFailures :: [ObligationResult] -> Either Text [Text]
renderFailures failures =
  fmap concat (mapM renderFailure (zip [1 :: Int ..] failures))
  where
    renderFailure (idx, res) = do
      let ob = orObligation res
      let cp = obCP ob
      overlapTxt <- renderDiagram (cpOverlap cp)
      leftTxt <- renderDiagram (cpLeft cp)
      rightTxt <- renderDiagram (cpRight cp)
      let header =
            [ ""
            , "  failure " <> T.pack (show idx) <> ": " <> cpRule1 cp <> " vs " <> cpRule2 cp <> " (" <> T.pack (show (obKind ob)) <> reasonSuffix (orWitness res) <> ")"
            , "  overlap:"
            , indent overlapTxt
            , "  left:"
            , indent leftTxt
            , "  right:"
            , indent rightTxt
            ]
      pure header

    reasonSuffix witness =
      case witness of
        SearchProved _ -> ""
        SearchUndecided lim -> ", " <> renderSearchLimit lim

indent :: Text -> Text
indent txt =
  let ls = T.lines txt
  in T.intercalate "\n" (map ("    " <>) ls)
