{-# LANGUAGE OverloadedStrings #-}
module Test.Backend
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.Backend
import Strat.Backend.Concat
import Strat.Kernel.Examples.Monoid as KMono
import Strat.Kernel.Syntax
import Strat.Kernel.Term


tests :: TestTree
tests =
  testGroup
    "Backend"
    [ testCase "evalTerm basic" testEval
    , testCase "compileTerm basic" testCompile
    , testCase "evalTerm unbound variable" testUnboundVar
    , testCase "evalTerm propagates op error" testOpError
    ]

testEval :: Assertion
testEval = do
  let model =
        Model
          { interpOp = \op _ -> Right (VAtom (case op of OpName t -> t))
          , interpSort = \_ -> Right (SortValue "ok")
          }
  case KMono.eTerm of
    Left err -> assertFailure (show err)
    Right e -> evalTerm model e @?= Right (VAtom "e")

testCompile :: Assertion
testCompile = do
  case KMono.eTerm of
    Left err -> assertFailure (show err)
    Right e -> compileTerm e @?= CatOp (OpName "e") []

testUnboundVar :: Assertion
testUnboundVar = do
  let model =
        Model
          { interpOp = \_ _ -> Right (VAtom "ok")
          , interpSort = \_ -> Right (SortValue "ok")
          }
  let term = mkVar KMono.objSort (Var (ScopeId "s") 0)
  evalTerm model term @?= Left (RuntimeError "unbound variable")

testOpError :: Assertion
testOpError = do
  let model =
        Model
          { interpOp = \_ _ -> Left (RuntimeError "bad op")
          , interpSort = \_ -> Right (SortValue "ok")
          }
  case KMono.eTerm of
    Left err -> assertFailure (show err)
    Right e -> evalTerm model e @?= Left (RuntimeError "bad op")
