{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Term.FragmentConfluence
  ( checkConfluentFragmentWithMapper
  , checkConfluentFragment
  , checkTypeTheoryConfluenceWithMapper
  , checkTypeTheoryConfluence
  , checkTypeTheoryNestedConfluenceWithMapper
  , checkTypeTheoryNestedConfluence
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.List as L
import qualified Data.Map.Strict as M
import Strat.Common.Rules (RuleClass(..))
import Strat.Poly.CriticalPairs
  ( CPMode(..)
  , CriticalPair(..)
  , CriticalPairInfo(..)
  , RuleInfo(..)
  , criticalPairsForRulesInTypeTheoryWithMapper
  , criticalPairsForRulesInTypeTheory
  )
import Strat.Poly.DefEq (normalizeTermDiagramWithMapper)
import Strat.Poly.DiagramIso (diagramIsoEq)
import Strat.Poly.Graph
  ( Diagram(..)
  , diagramPortObj
  )
import Strat.Poly.Obj (TermDiagram(..))
import Strat.Poly.Rewrite (RewriteRule(..))
import Strat.Poly.Term.RuleDiagram (SpliceMapper, sameModeSpliceMapper)
import Strat.Poly.TypeTheory (DefFragment(..), TmRule(..), TypeTheory(..))

data PairBad = PairBad
  { pbRule1 :: Text
  , pbRule2 :: Text
  , pbLeftNF :: Diagram
  , pbRightNF :: Diagram
  }

checkConfluentFragmentWithMapper :: SpliceMapper -> TypeTheory -> DefFragment -> Either Text ()
checkConfluentFragmentWithMapper spliceMapper tt fragment = do
  bad <- badPairs spliceMapper tt fragment
  if null bad
    then Right ()
    else
      Left
        ( "confluence failed for mode "
            <> T.pack (show (dfMode fragment))
            <> ": found non-joinable critical pair\n"
            <> renderBadPairs bad
        )

checkConfluentFragment :: TypeTheory -> DefFragment -> Either Text ()
checkConfluentFragment =
  checkConfluentFragmentWithMapper (sameModeSpliceMapper "confluence")

checkTypeTheoryConfluenceWithMapper :: SpliceMapper -> TypeTheory -> Either Text ()
checkTypeTheoryConfluenceWithMapper spliceMapper tt =
  mapM_ (checkConfluentFragmentWithMapper spliceMapper tt) (M.elems (ttDefFragments tt))

checkTypeTheoryConfluence :: TypeTheory -> Either Text ()
checkTypeTheoryConfluence =
  checkTypeTheoryConfluenceWithMapper (sameModeSpliceMapper "confluence")

checkTypeTheoryNestedConfluenceWithMapper :: SpliceMapper -> TypeTheory -> Either Text ()
checkTypeTheoryNestedConfluenceWithMapper =
  checkTypeTheoryConfluenceWithMapper

checkTypeTheoryNestedConfluence :: TypeTheory -> Either Text ()
checkTypeTheoryNestedConfluence =
  checkTypeTheoryNestedConfluenceWithMapper (sameModeSpliceMapper "confluence")

badPairs :: SpliceMapper -> TypeTheory -> DefFragment -> Either Text [PairBad]
badPairs spliceMapper tt fragment = do
  pairs <- criticalPairsForRulesInTypeTheoryWithMapper tt spliceMapper CP_All rules
  fmap concat (mapM checkPair pairs)
  where
    rules :: [RuleInfo]
    rules =
      [ RuleInfo
          { riLabel = ruleLabel i
          , riRule = tmRuleToRewriteRule (ruleLabel i) rule
          , riClass = Computational
          }
      | (i, rule) <- zip [0 :: Int ..] (dfRules fragment)
      ]

    checkPair pairInfo = do
      let pair = cpiPair pairInfo
          left = cpLeft pair
          right = cpRight pair
      leftNF <- normalizeTermSide spliceMapper tt left
      rightNF <- normalizeTermSide spliceMapper tt right
      same <- diagramIsoEq leftNF rightNF
      pure
        [ PairBad (cpRule1 pair) (cpRule2 pair) leftNF rightNF
        | not same
        ]

ruleLabel :: Int -> Text
ruleLabel i = "tmrule." <> T.pack (show i)

tmRuleToRewriteRule :: Text -> TmRule -> RewriteRule
tmRuleToRewriteRule label rule =
  RewriteRule
    { rrName = label
    , rrLHS = unTermDiagram (trLHS rule)
    , rrRHS = unTermDiagram (trRHS rule)
    , rrTyVars = trTyVars rule
    , rrTmVars = trVars rule
    }

unTermDiagram :: TermDiagram -> Diagram
unTermDiagram (TermDiagram diag) = diag

normalizeTermSide :: SpliceMapper -> TypeTheory -> Diagram -> Either Text Diagram
normalizeTermSide spliceMapper tt diag = do
  outPid <-
    case dOut diag of
      [pid] -> Right pid
      _ -> Left "confluence: nested critical-pair branch is not a single-output term"
  outTy <-
    case diagramPortObj diag outPid of
      Just ty -> Right ty
      Nothing -> Left "confluence: nested critical-pair branch is missing an output sort"
  term <- normalizeTermDiagramWithMapper tt spliceMapper (dTmCtx diag) outTy (TermDiagram diag)
  pure (unTermDiagram term)

renderBadPairs :: [PairBad] -> Text
renderBadPairs bad =
  T.intercalate
    "\n"
    [ "  "
        <> pbRule1 one
        <> " overlaps "
        <> pbRule2 one
        <> " -> nf(left)="
        <> T.pack (show (pbLeftNF one))
        <> ", nf(right)="
        <> T.pack (show (pbRightNF one))
    | one <- L.take 10 bad
    ]
