{-# LANGUAGE OverloadedStrings #-}
module Test.Kernel.FreeTele
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.Kernel.FreeTele (freeTeleOfTerm)
import Strat.Kernel.Syntax (Binder(..), Var(..), ScopeId(..))
import Strat.Kernel.Term (mkVar)
import Test.Kernel.Fixtures (objSort, homSort)


tests :: TestTree
tests =
  testGroup
    "Kernel.FreeTele"
    [ testCase "vars in sort indices included" testVarsInSortIndices
    , testCase "detect cyclic sort dependency" testCycleDetect
    ]


testVarsInSortIndices :: Assertion
testVarsInSortIndices = do
  let vx = Var (ScopeId "tele:x") 0
  let vy = Var (ScopeId "tele:y") 1
  let xTerm = mkVar objSort vx
  let ySort = homSort xTerm xTerm
  let yTerm = mkVar ySort vy
  tele <-
    case freeTeleOfTerm yTerm of
      Left err -> assertFailure ("freeTeleOfTerm failed: " <> show err)
      Right t -> pure t
  let vars = map bVar tele
  vars @?= [vx, vy]


testCycleDetect :: Assertion
testCycleDetect = do
  let vx = Var (ScopeId "tele:x") 0
  let xTerm = mkVar objSort vx
  let xSort = homSort xTerm xTerm
  let xBad = mkVar xSort vx
  case freeTeleOfTerm xBad of
    Left _ -> pure ()
    Right _ -> assertFailure "expected cycle detection error"
