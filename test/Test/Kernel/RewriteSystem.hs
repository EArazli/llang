{-# LANGUAGE OverloadedStrings #-}
module Test.Kernel.RewriteSystem
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.Kernel.Presentation
import Strat.Kernel.RewriteSystem
import Strat.Kernel.Rule
import Strat.Kernel.Syntax
import Strat.Kernel.Term
import Strat.Kernel.Types
import Data.Text (Text)
import Test.Kernel.Fixtures

tests :: TestTree
tests =
  testGroup
    "Kernel.RewriteSystem"
    [ testCase "compile RL orientation" testCompileRL
    , testCase "compile bidirectional" testCompileBidirectional
    , testCase "compile unoriented skipped" testCompileUnoriented
    , testCase "structural as bidirectional" testCompileStructuralBidir
    , testCase "UseOnlyComputationalLR skips RL" testCompileSkipRL
    , testCase "UseOnlyComputationalLR skips structural" testCompileSkipStructural
    , testCase "duplicate eq names rejected" testDuplicateEqNames
    , testCase "out-of-scope vars rejected" testOutOfScopeVars
    , testCase "equation sort mismatch rejected" testSortMismatch
    ]

mkEq1 :: Text -> RuleClass -> Orientation -> (Term -> Term) -> (Term -> Term) -> Equation
mkEq1 name cls orient lhsF rhsF =
  let scope = ScopeId ("eq:" <> name)
      vx = Var scope 0
      x = mkVar objSort vx
  in Equation
      { eqName = name
      , eqClass = cls
      , eqOrient = orient
      , eqTele = [Binder vx objSort]
      , eqLHS = lhsF x
      , eqRHS = rhsF x
      }

basePres :: [Equation] -> Presentation
basePres eqs =
  Presentation
    { presName = "P"
    , presSig = sigBasic
    , presEqs = eqs
    }

testCompileRL :: Assertion
testCompileRL = do
  let eq = mkEq1 "r" Computational RL id id
  case compileRewriteSystem UseAllOriented (basePres [eq]) of
    Left err -> assertFailure (show err)
    Right rs -> map ruleId (rsRules rs) @?= [RuleId "r" DirRL]

testCompileBidirectional :: Assertion
testCompileBidirectional = do
  let eq = mkEq1 "r" Computational Bidirectional id id
  case compileRewriteSystem UseAllOriented (basePres [eq]) of
    Left err -> assertFailure (show err)
    Right rs -> map ruleId (rsRules rs) @?= [RuleId "r" DirLR, RuleId "r" DirRL]

testCompileUnoriented :: Assertion
testCompileUnoriented = do
  let eq = mkEq1 "r" Computational Unoriented id id
  case compileRewriteSystem UseAllOriented (basePres [eq]) of
    Left err -> assertFailure (show err)
    Right rs -> rsRules rs @?= []

testCompileStructuralBidir :: Assertion
testCompileStructuralBidir = do
  let eq = mkEq1 "r" Structural Unoriented id id
  case compileRewriteSystem UseStructuralAsBidirectional (basePres [eq]) of
    Left err -> assertFailure (show err)
    Right rs -> map ruleId (rsRules rs) @?= [RuleId "r" DirLR, RuleId "r" DirRL]

testCompileSkipRL :: Assertion
testCompileSkipRL = do
  let eq = mkEq1 "r" Computational RL id id
  case compileRewriteSystem UseOnlyComputationalLR (basePres [eq]) of
    Left err -> assertFailure (show err)
    Right rs -> rsRules rs @?= []

testCompileSkipStructural :: Assertion
testCompileSkipStructural = do
  let eq = mkEq1 "r" Structural LR id id
  case compileRewriteSystem UseOnlyComputationalLR (basePres [eq]) of
    Left err -> assertFailure (show err)
    Right rs -> rsRules rs @?= []

testDuplicateEqNames :: Assertion
testDuplicateEqNames = do
  let eq1 = mkEq1 "r" Computational LR id id
  let eq2 = mkEq1 "r" Computational LR id id
  case compileRewriteSystem UseOnlyComputationalLR (basePres [eq1, eq2]) of
    Left _ -> pure ()
    Right _ -> assertFailure "expected duplicate eq name error"

testOutOfScopeVars :: Assertion
testOutOfScopeVars = do
  let scope = ScopeId "eq:oops"
  let vx = Var scope 0
  let x = mkVar objSort vx
  let eq =
        Equation
          { eqName = "bad"
          , eqClass = Computational
          , eqOrient = LR
          , eqTele = []
          , eqLHS = mkTerm sigBasic "f" [x]
          , eqRHS = mkTerm sigBasic "g" [x]
          }
  case compileRewriteSystem UseAllOriented (basePres [eq]) of
    Left _ -> pure ()
    Right _ -> assertFailure "expected out-of-scope var error"

testSortMismatch :: Assertion
testSortMismatch = do
  let a = mkTerm sigBasic "a" []
  let ida = mkTerm sigBasic "id" [a]
  let eq =
        Equation
          { eqName = "badSort"
          , eqClass = Computational
          , eqOrient = LR
          , eqTele = []
          , eqLHS = a
          , eqRHS = ida
          }
  case compileRewriteSystem UseAllOriented (basePres [eq]) of
    Left _ -> pure ()
    Right _ -> assertFailure "expected sort mismatch error"
