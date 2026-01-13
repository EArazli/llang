{-# LANGUAGE OverloadedStrings #-}
module Strat.Meta.Examples.Monoid where

import Strat.Meta.CriticalPairs
import Strat.Meta.Presentation
import Strat.Meta.RewriteSystem
import Strat.Meta.Rule
import Strat.Meta.Term.FO
import Strat.Meta.Types
import Data.Text (Text)

eSym :: Sym
eSym = Sym "e"

mSym :: Sym
mSym = Sym "m"

eTerm :: Term
eTerm = TApp eSym []

mTerm :: Term -> Term -> Term
mTerm a b = TApp mSym [a, b]

mkVar :: Text -> Int -> Term
mkVar name n =
  let ns = Ns (RuleId name DirLR) 0
  in TVar (V ns n)

monoidPresentation :: Presentation Term
monoidPresentation =
  Presentation
    { presName = "Monoid"
    , presEqs = [leftUnit, rightUnit, assoc]
    }
  where
    leftUnit =
      let x = mkVar "left-unit" 0
      in Equation
          { eqName = "left-unit"
          , eqClass = Computational
          , eqOrient = LR
          , eqLHS = mTerm eTerm x
          , eqRHS = x
          }
    rightUnit =
      let x = mkVar "right-unit" 0
      in Equation
          { eqName = "right-unit"
          , eqClass = Computational
          , eqOrient = LR
          , eqLHS = mTerm x eTerm
          , eqRHS = x
          }
    assoc =
      let x = mkVar "assoc" 0
          y = mkVar "assoc" 1
          z = mkVar "assoc" 2
      in Equation
          { eqName = "assoc"
          , eqClass = Computational
          , eqOrient = LR
          , eqLHS = mTerm (mTerm x y) z
          , eqRHS = mTerm x (mTerm y z)
          }

monoidRewriteSystem :: Either Text (RewriteSystem Term)
monoidRewriteSystem = compileRewriteSystem UseOnlyComputationalLR monoidPresentation

monoidCriticalPairs :: Either Text [CriticalPair Term]
monoidCriticalPairs = do
  rs <- monoidRewriteSystem
  criticalPairs CP_All (getRule rs) rs
