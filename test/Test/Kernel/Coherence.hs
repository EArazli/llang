{-# LANGUAGE OverloadedStrings #-}
module Test.Kernel.Coherence
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.Kernel.Coherence
import Strat.Kernel.CriticalPairs
import Strat.Kernel.Presentation
import Strat.Kernel.Rewrite
import Strat.Kernel.RewriteSystem
import Strat.Kernel.Rule
import Strat.Kernel.Types
import qualified Data.List as L
import Data.Text (Text)
import Test.Kernel.Fixtures

tests :: TestTree
tests =
  testGroup
    "Kernel.Coherence"
    [ testCase "validateJoiner succeeds" testValidateJoiner
    , testCase "validateJoiner fails" testValidateJoinerFail
    ]

mkEqConst :: Text -> Text -> Text -> Equation
mkEqConst name l r =
  Equation
    { eqName = name
    , eqClass = Computational
    , eqOrient = LR
    , eqTele = []
    , eqLHS = mkTerm sigBasic l []
    , eqRHS = mkTerm sigBasic r []
    }

mkRS :: [Equation] -> RewriteSystem
mkRS eqs =
  case compileRewriteSystem UseAllOriented (Presentation "P" sigBasic eqs) of
    Left err -> error (show err)
    Right rs -> rs

testValidateJoiner :: Assertion
testValidateJoiner = do
  let eq1 = mkEqConst "r1" "a" "b"
  let eq2 = mkEqConst "r2" "a" "c"
  let eq3 = mkEqConst "r3" "b" "c"
  let rs = mkRS [eq1, eq2, eq3]
  case criticalPairs CP_All rs of
    Left err -> assertFailure (show err)
    Right cps -> do
      let target =
            L.find
              (\cp -> cpRule1 cp == RuleId "r1" DirLR && cpRule2 cp == RuleId "r2" DirLR)
              cps
      case target of
        Nothing -> assertFailure "expected critical pair"
        Just cp -> do
          let leftStep =
                case rewriteOnce rs (cpLeft cp) of
                  (r : _) -> redexStep r
                  [] -> error "expected left redex"
          let joiner =
                Joiner
                  { joinTerm = mkTerm sigBasic "c" []
                  , leftDerivation = [leftStep]
                  , rightDerivation = []
                  }
          validateJoiner rs cp joiner @?= True

testValidateJoinerFail :: Assertion
testValidateJoinerFail = do
  let eq1 = mkEqConst "r1" "a" "b"
  let eq2 = mkEqConst "r2" "a" "c"
  let eq3 = mkEqConst "r3" "b" "c"
  let rs = mkRS [eq1, eq2, eq3]
  case criticalPairs CP_All rs of
    Left err -> assertFailure (show err)
    Right cps ->
      case L.find (\cp -> cpRule1 cp == RuleId "r1" DirLR && cpRule2 cp == RuleId "r2" DirLR) cps of
        Nothing -> assertFailure "expected critical pair"
        Just cp -> do
          let badJoiner =
                Joiner
                  { joinTerm = mkTerm sigBasic "b" []
                  , leftDerivation = []
                  , rightDerivation = []
                  }
          validateJoiner rs cp badJoiner @?= False
