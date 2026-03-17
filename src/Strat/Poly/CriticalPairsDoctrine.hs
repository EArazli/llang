{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.CriticalPairsDoctrine
  ( criticalPairsForDoctrine
  ) where

import Data.Text (Text)
import Strat.Common.Rules
  ( Orientation(..)
  , RewritePolicy(..)
  , RuleClass(..)
  )
import Strat.Poly.Cell2
  ( Cell2(..)
  , c2TyVars
  , c2TmVars
  )
import Strat.Poly.CriticalPairs
  ( CPMode
  , CriticalPairInfo
  , RuleInfo(..)
  , criticalPairsForRulesInTypeTheoryWithMapper
  , criticalPairsForRulesInTypeTheory
  )
import Strat.Poly.Doctrine
  ( Doctrine(..)
  , doctrineTypeTheory
  )
import Strat.Poly.ModAction (applyModExpr)
import Strat.Poly.Rewrite
  ( RewriteRule(..)
  )

criticalPairsForDoctrine :: CPMode -> RewritePolicy -> Doctrine -> Either Text [CriticalPairInfo]
criticalPairsForDoctrine mode policy doc = do
  tt <- doctrineTypeTheory doc
  criticalPairsForRulesInTypeTheoryWithMapper tt (applyModExpr doc) mode (rulesWithClass policy (dCells2 doc))

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
          rule =
            RewriteRule
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
