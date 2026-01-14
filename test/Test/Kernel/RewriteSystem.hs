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
    , testCase "variable condition violated LR rejected" testVarConditionLR
    , testCase "variable condition violated RL rejected" testVarConditionRL
    , testCase "variable condition violated bidirectional rejected" testVarConditionBidir
    , testCase "invalid cached term sort rejected" testInvalidCachedSort
    , testCase "invalid sort index rejected" testInvalidSortIndex
    , testCase "binder sort mismatch rejected" testBinderSortMismatch
    , testCase "binder sort refers to later binder rejected" testBinderSortLate
    , testCase "binder sort out-of-scope var rejected" testBinderSortOutOfScope
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

testVarConditionLR :: Assertion
testVarConditionLR = do
  let scope = ScopeId "eq:r"
  let vx = Var scope 0
  let vy = Var scope 1
  let x = mkVar objSort vx
  let y = mkVar objSort vy
  let eq =
        Equation
          { eqName = "r"
          , eqClass = Computational
          , eqOrient = LR
          , eqTele = [Binder vx objSort, Binder vy objSort]
          , eqLHS = mkTerm sigBasic "f" [x]
          , eqRHS = mkTerm sigBasic "g" [y]
          }
  case compileRewriteSystem UseAllOriented (basePres [eq]) of
    Left _ -> pure ()
    Right _ -> assertFailure "expected variable condition error"

testVarConditionRL :: Assertion
testVarConditionRL = do
  let scope = ScopeId "eq:r"
  let vx = Var scope 0
  let vy = Var scope 1
  let x = mkVar objSort vx
  let y = mkVar objSort vy
  let eq =
        Equation
          { eqName = "r"
          , eqClass = Computational
          , eqOrient = RL
          , eqTele = [Binder vx objSort, Binder vy objSort]
          , eqLHS = mkTerm sigBasic "f" [x]
          , eqRHS = mkTerm sigBasic "g" [y]
          }
  case compileRewriteSystem UseAllOriented (basePres [eq]) of
    Left _ -> pure ()
    Right _ -> assertFailure "expected variable condition error"

testVarConditionBidir :: Assertion
testVarConditionBidir = do
  let scope = ScopeId "eq:r"
  let vx = Var scope 0
  let vy = Var scope 1
  let x = mkVar objSort vx
  let y = mkVar objSort vy
  let eq =
        Equation
          { eqName = "r"
          , eqClass = Computational
          , eqOrient = Bidirectional
          , eqTele = [Binder vx objSort, Binder vy objSort]
          , eqLHS = mkTerm sigBasic "f" [x]
          , eqRHS = mkTerm sigBasic "m" [x, y]
          }
  case compileRewriteSystem UseAllOriented (basePres [eq]) of
    Left _ -> pure ()
    Right _ -> assertFailure "expected variable condition error"

testInvalidCachedSort :: Assertion
testInvalidCachedSort = do
  let a = mkTerm sigBasic "a" []
  let badTerm = Term { termSort = homSort a a, termNode = TOp opA [] }
  let eq =
        Equation
          { eqName = "badSortCache"
          , eqClass = Computational
          , eqOrient = LR
          , eqTele = []
          , eqLHS = badTerm
          , eqRHS = badTerm
          }
  case compileRewriteSystem UseAllOriented (basePres [eq]) of
    Left _ -> pure ()
    Right _ -> assertFailure "expected invalid cached sort error"

testInvalidSortIndex :: Assertion
testInvalidSortIndex = do
  let a = mkTerm sigBasic "a" []
  let ida = mkTerm sigBasic "id" [a]
  let badSort = Sort homName [a, ida]
  let v = Var (ScopeId "eq:badIdx") 0
  let term = mkVar badSort v
  let eq =
        Equation
          { eqName = "badIdx"
          , eqClass = Computational
          , eqOrient = LR
          , eqTele = [Binder v badSort]
          , eqLHS = term
          , eqRHS = term
          }
  case compileRewriteSystem UseAllOriented (basePres [eq]) of
    Left _ -> pure ()
    Right _ -> assertFailure "expected invalid sort index error"

testBinderSortMismatch :: Assertion
testBinderSortMismatch = do
  let a = mkTerm sigBasic "a" []
  let scope = ScopeId "eq:badBind"
  let vx = Var scope 0
  let xBad = mkVar (homSort a a) vx
  let badTerm = Term { termSort = objSort, termNode = TOp opF [xBad] }
  let eq =
        Equation
          { eqName = "badBind"
          , eqClass = Computational
          , eqOrient = LR
          , eqTele = [Binder vx objSort]
          , eqLHS = badTerm
          , eqRHS = badTerm
          }
  case compileRewriteSystem UseAllOriented (basePres [eq]) of
    Left _ -> pure ()
    Right _ -> assertFailure "expected binder sort mismatch error"

testBinderSortLate :: Assertion
testBinderSortLate = do
  let scope = ScopeId "eq:late"
  let vx = Var scope 0
  let vy = Var scope 1
  let y = mkVar objSort vy
  let badSort = homSort y y
  let eq =
        Equation
          { eqName = "late"
          , eqClass = Computational
          , eqOrient = LR
          , eqTele = [Binder vx badSort, Binder vy objSort]
          , eqLHS = mkVar badSort vx
          , eqRHS = mkVar badSort vx
          }
  case compileRewriteSystem UseAllOriented (basePres [eq]) of
    Left _ -> pure ()
    Right _ -> assertFailure "expected late binder sort error"

testBinderSortOutOfScope :: Assertion
testBinderSortOutOfScope = do
  let scope = ScopeId "eq:oob"
  let vx = Var scope 0
  let vz = Var (ScopeId "eq:oob:z") 2
  let z = mkVar objSort vz
  let badSort = homSort z z
  let eq =
        Equation
          { eqName = "oob"
          , eqClass = Computational
          , eqOrient = LR
          , eqTele = [Binder vx badSort]
          , eqLHS = mkVar badSort vx
          , eqRHS = mkVar badSort vx
          }
  case compileRewriteSystem UseAllOriented (basePres [eq]) of
    Left _ -> pure ()
    Right _ -> assertFailure "expected out-of-scope binder sort error"
