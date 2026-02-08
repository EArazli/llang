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
import Strat.Poly.Normalize (JoinWitness(..), joinableWithinWitness)
import Strat.Poly.Rewrite (rulesFromPolicy, RewriteRule)
import Strat.Poly.Doctrine (Doctrine(..))
import Strat.Poly.ModeTheory (ModeTheory)
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
  , orWitness :: Maybe JoinWitness
  } deriving (Eq, Show)

checkCoherence :: CPMode -> RewritePolicy -> Int -> Doctrine -> Either Text [ObligationResult]
checkCoherence mode policy fuel doc = do
  cps <- criticalPairsForDoctrine mode policy doc
  let obligations = concatMap (obligationsFor mode) cps
  let rules = rulesFromPolicy policy (dCells2 doc)
  mapM (checkObligation (dModes doc) fuel rules) obligations

obligationsFor :: CPMode -> CriticalPairInfo -> [Obligation]
obligationsFor mode info =
  case (cpiClass1 info, cpiClass2 info) of
    (Structural, Structural) -> [Obligation NeedsCommute (cpiPair info)]
    (Structural, Computational) -> [Obligation NeedsJoin (cpiPair info)]
    (Computational, Structural) -> [Obligation NeedsJoin (cpiPair info)]
    (Computational, Computational) ->
      if mode == CP_All then [Obligation NeedsJoin (cpiPair info)] else []

checkObligation :: ModeTheory -> Int -> [RewriteRule] -> Obligation -> Either Text ObligationResult
checkObligation mt fuel rules ob = do
  mW <- joinableWithinWitness mt fuel rules (cpLeft (obCP ob)) (cpRight (obCP ob))
  pure ObligationResult { orObligation = ob, orWitness = mW }

renderCoherenceReport :: [ObligationResult] -> Either Text Text
renderCoherenceReport results = do
  let total = length results
  let joins = length [() | r <- results, obKind (orObligation r) == NeedsJoin]
  let commutes = length [() | r <- results, obKind (orObligation r) == NeedsCommute]
  let failures = [ r | r <- results, orWitness r == Nothing ]
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
            , "  failure " <> T.pack (show idx) <> ": " <> cpRule1 cp <> " vs " <> cpRule2 cp <> " (" <> T.pack (show (obKind ob)) <> ")"
            , "  overlap:"
            , indent overlapTxt
            , "  left:"
            , indent leftTxt
            , "  right:"
            , indent rightTxt
            ]
      pure header

indent :: Text -> Text
indent txt =
  let ls = T.lines txt
  in T.intercalate "\n" (map ("    " <>) ls)
