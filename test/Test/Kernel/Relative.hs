{-# LANGUAGE OverloadedStrings #-}
module Test.Kernel.Relative
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.Kernel.Coherence
import Strat.Kernel.Presentation
import Strat.Kernel.Relative
import Strat.Kernel.RewriteSystem
import Strat.Kernel.Rule
import Strat.Kernel.Signature
import Strat.Kernel.Syntax
import Strat.Kernel.Term
import Strat.Kernel.Types
import Data.Text (Text)
import Test.Kernel.Fixtures

tests :: TestTree
tests =
  testGroup
    "Kernel.Relative"
    [ testCase "normalizeW" testNormalizeW
    , testCase "normalizeR_mod_W" testNormalizeRModW
    , testCase "relative obligations" testRelativeObligations
    ]

relSig :: Signature
relSig = sigBasic

relTerm :: Text -> [Term] -> Term
relTerm name args = mkTerm relSig name args

mkEq1Class :: Text -> RuleClass -> (Term -> Term) -> (Term -> Term) -> Equation
mkEq1Class name cls lhsF rhsF =
  let scope = ScopeId ("eq:" <> name)
      vx = Var scope 0
      x = mkVar objSort vx
  in Equation
      { eqName = name
      , eqClass = cls
      , eqOrient = LR
      , eqTele = [Binder vx objSort]
      , eqLHS = lhsF x
      , eqRHS = rhsF x
      }

testNormalizeW :: Assertion
testNormalizeW = do
  let eqStruct = mkEq1Class "struct" Structural (\x -> relTerm "f" [x]) id
  let eqComp = mkEq1Class "comp" Computational (\x -> relTerm "g" [x]) (\x -> relTerm "h" [x])
  let pres = Presentation "Rel" relSig [eqStruct, eqComp]
  case compileRewriteSystem UseAllOriented pres of
    Left err -> assertFailure (show err)
    Right rs -> do
      let t = relTerm "g" [relTerm "f" [relTerm "a" []]]
      normalizeW 1 rs t @?= relTerm "g" [relTerm "a" []]

testNormalizeRModW :: Assertion
testNormalizeRModW = do
  let eqStruct = mkEq1Class "struct" Structural (\x -> relTerm "f" [x]) id
  let eqComp = mkEq1Class "comp" Computational (\x -> relTerm "g" [x]) (\x -> relTerm "h" [x])
  let pres = Presentation "Rel" relSig [eqStruct, eqComp]
  case compileRewriteSystem UseAllOriented pres of
    Left err -> assertFailure (show err)
    Right rs -> do
      let t = relTerm "g" [relTerm "f" [relTerm "a" []]]
      normalizeR_mod_W 1 rs t @?= relTerm "h" [relTerm "a" []]

testRelativeObligations :: Assertion
testRelativeObligations = do
  let eqStruct = mkEq1Class "struct" Structural (\x -> relTerm "f" [x]) id
  let eqComp = mkEq1Class "comp" Computational (\x -> relTerm "f" [x]) (\x -> relTerm "g" [x])
  let pres = Presentation "RelObs" relSig [eqStruct, eqComp]
  case compileRewriteSystem UseAllOriented pres of
    Left err -> assertFailure (show err)
    Right rs ->
      case relativeObligations rs of
        Left err -> assertFailure (show err)
        Right obs -> do
          assertBool "expected NeedsCommute" (any ((== NeedsCommute) . obKind) obs)
          assertBool "expected NeedsJoin" (any ((== NeedsJoin) . obKind) obs)
