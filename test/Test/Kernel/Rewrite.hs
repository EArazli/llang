{-# LANGUAGE OverloadedStrings #-}
module Test.Kernel.Rewrite
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.Kernel.Presentation
import Strat.Kernel.Rewrite
import Strat.Kernel.RewriteSystem
import Strat.Kernel.Rule
import Strat.Kernel.Syntax
import Strat.Kernel.Term
import Strat.Kernel.Types
import Strat.Kernel.Rewrite.Indexed as Indexed
import Data.Text (Text)
import qualified Data.Map.Strict as M
import Test.Kernel.Fixtures

tests :: TestTree
tests =
  testGroup
    "Kernel.Rewrite"
    [ testCase "rewriteOnce ordering" testRewriteOnceOrdering
    , testCase "chooseRedex prefers outermost" testChooseRedexOutermost
    , testCase "chooseRedex tie-breaks by ruleIx" testChooseRedexRuleIx
    , testCase "applyStep strict" testApplyStepStrict
    , testCase "normalize uses chooseRedex" testNormalizeUsesChooseRedex
    , testCase "rewriteOnce indexed equals rewriteOnce" testRewriteOnceIndexed
    ]

mkEqConst :: Text -> RuleClass -> Orientation -> Text -> Text -> Equation
mkEqConst name cls orient l r =
  let lhsTerm = mkTerm sigBasic l []
      rhsTerm = mkTerm sigBasic r []
  in Equation
      { eqName = name
      , eqClass = cls
      , eqOrient = orient
      , eqTele = []
      , eqLHS = lhsTerm
      , eqRHS = rhsTerm
      }

mkEqUnary :: Text -> Text -> Text -> Equation
mkEqUnary name lhsOp rhsOp =
  let scope = ScopeId ("eq:" <> name)
      vx = Var scope 0
      x = mkVar objSort vx
  in Equation
      { eqName = name
      , eqClass = Computational
      , eqOrient = LR
      , eqTele = [Binder vx objSort]
      , eqLHS = mkTerm sigBasic lhsOp [x]
      , eqRHS = mkTerm sigBasic rhsOp [x]
      }

mkEqBinary :: Text -> Text -> (Term -> Term -> Term) -> Equation
mkEqBinary name lhsOp rhsF =
  let scope = ScopeId ("eq:" <> name)
      vx = Var scope 0
      vy = Var scope 1
      x = mkVar objSort vx
      y = mkVar objSort vy
  in Equation
      { eqName = name
      , eqClass = Computational
      , eqOrient = LR
      , eqTele = [Binder vx objSort, Binder vy objSort]
      , eqLHS = mkTerm sigBasic lhsOp [x, y]
      , eqRHS = rhsF x y
      }

mkRS :: [Equation] -> RewriteSystem
mkRS eqs =
  case compileRewriteSystem UseAllOriented (Presentation "P" sigBasic eqs) of
    Left err -> error (show err)
    Right rs -> rs

testRewriteOnceOrdering :: Assertion
testRewriteOnceOrdering = do
  let eqInner = mkEqConst "r1" Computational LR "a" "b"
  let eqOuter = mkEqBinary "r2" "m" (\x _ -> mkTerm sigBasic "f" [x])
  let rs = mkRS [eqInner, eqOuter]
  let term = mkTerm sigBasic "m" [mkTerm sigBasic "a" [], mkTerm sigBasic "a" []]
  let reds = rewriteOnce rs term
  map (stepRule . redexStep) reds
    @?= [ RuleId "r1" DirLR
        , RuleId "r1" DirLR
        , RuleId "r2" DirLR
        ]
  map (stepPos . redexStep) reds @?= [[0], [1], []]

testChooseRedexOutermost :: Assertion
testChooseRedexOutermost = do
  let eqInner = mkEqConst "r1" Computational LR "a" "b"
  let eqOuter = mkEqBinary "r2" "m" (\x _ -> mkTerm sigBasic "f" [x])
  let rs = mkRS [eqInner, eqOuter]
  let term = mkTerm sigBasic "m" [mkTerm sigBasic "a" [], mkTerm sigBasic "a" []]
  let reds = rewriteOnce rs term
  case chooseRedex reds of
    Nothing -> assertFailure "expected redex"
    Just r -> stepRule (redexStep r) @?= RuleId "r2" DirLR

testChooseRedexRuleIx :: Assertion
testChooseRedexRuleIx = do
  let eq1 = mkEqConst "r1" Computational LR "a" "b"
  let eq2 = mkEqConst "r2" Computational LR "a" "c"
  let rs = mkRS [eq1, eq2]
  let term = mkTerm sigBasic "a" []
  let reds = rewriteOnce rs term
  case chooseRedex reds of
    Nothing -> assertFailure "expected redex"
    Just r -> stepRule (redexStep r) @?= RuleId "r1" DirLR

testApplyStepStrict :: Assertion
testApplyStepStrict = do
  let eq = mkEqUnary "r" "f" "g"
  let rs = mkRS [eq]
  let rule = getRule rs (RuleId "r" DirLR)
  let badStep =
        Step
          { stepRule = ruleId rule
          , stepPos = []
          , stepSubst = M.empty
          }
  let term = mkTerm sigBasic "h" [mkTerm sigBasic "a" []]
  applyStep (getRule rs) badStep term @?= Nothing

testNormalizeUsesChooseRedex :: Assertion
testNormalizeUsesChooseRedex = do
  let eqInner = mkEqConst "r1" Computational LR "a" "b"
  let eqOuter = mkEqBinary "r2" "m" (\x _ -> mkTerm sigBasic "f" [x])
  let rs = mkRS [eqInner, eqOuter]
  let term = mkTerm sigBasic "m" [mkTerm sigBasic "a" [], mkTerm sigBasic "a" []]
  normalize 1 rs term @?= mkTerm sigBasic "f" [mkTerm sigBasic "a" []]

testRewriteOnceIndexed :: Assertion
testRewriteOnceIndexed = do
  let eqInner = mkEqConst "r1" Computational LR "a" "b"
  let eqOuter = mkEqBinary "r2" "m" (\x _ -> mkTerm sigBasic "f" [x])
  let rs = mkRS [eqInner, eqOuter]
  let idx = Indexed.buildRuleIndex rs
  let term = mkTerm sigBasic "m" [mkTerm sigBasic "a" [], mkTerm sigBasic "a" []]
  rewriteOnce rs term @?= Indexed.rewriteOnceIndexed rs idx term
