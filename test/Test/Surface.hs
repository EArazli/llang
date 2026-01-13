{-# LANGUAGE OverloadedStrings #-}
module Test.Surface
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.Surface
import Strat.Surface.Combinator
import Strat.Kernel.Examples.Monoid as KMono
import Strat.Kernel.Syntax
import Strat.Kernel.Term (mkVar)
import qualified Data.Map.Strict as M

tests :: TestTree
tests =
  testGroup
    "Surface"
    [ testCase "combinator elaborates" testElab
    , testCase "combinator unknown op" testUnknownOp
    , testCase "combinator unknown var" testUnknownVar
    , testCase "combinator type error" testTypeError
    ]

testElab :: Assertion
testElab = do
  let scope = ScopeId "surf"
  let vx = Var scope 0
  let x = mkVar KMono.objSort vx
  let inst = withVars (M.fromList [("x", x)]) (defaultInstance KMono.presMonoid)
  let term = COp "m" [COp "e" [], CVar "x"]
  case (elaborate inst term, KMono.eTerm) of
    (Right t, Right e) ->
      case KMono.mTerm e x of
        Left err -> assertFailure (show err)
        Right expected -> t @?= expected
    (Left err, _) -> assertFailure (show err)
    (_, Left err) -> assertFailure (show err)

testUnknownOp :: Assertion
testUnknownOp = do
  let inst = defaultInstance KMono.presMonoid
  case elaborate inst (COp "missing" []) of
    Left (UnknownOp _) -> pure ()
    Left err -> assertFailure (show err)
    Right _ -> assertFailure "expected unknown op error"

testUnknownVar :: Assertion
testUnknownVar = do
  let inst = defaultInstance KMono.presMonoid
  case elaborate inst (CVar "x") of
    Left (UnknownVar _) -> pure ()
    Left err -> assertFailure (show err)
    Right _ -> assertFailure "expected unknown var error"

testTypeError :: Assertion
testTypeError = do
  let inst = defaultInstance KMono.presMonoid
  case elaborate inst (COp "m" [COp "e" []]) of
    Left (ElabTypeError _) -> pure ()
    Left err -> assertFailure (show err)
    Right _ -> assertFailure "expected type error"
