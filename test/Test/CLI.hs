{-# LANGUAGE OverloadedStrings #-}
module Test.CLI
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.CLI
import Strat.Backend (Value(..))
import Strat.Backend.Concat (CatExpr(..))
import Strat.Kernel.RewriteSystem (RewritePolicy(..))
import Strat.Kernel.Syntax
import qualified Data.Text as T
import Paths_llang (getDataFileName)


tests :: TestTree
tests =
  testGroup
    "CLI"
    [ testCase "end-to-end example" testEndToEnd ]


testEndToEnd :: Assertion
testEndToEnd = do
  path <- getDataFileName "examples/monoid.llang"
  let opts =
        CLIOptions
          { optFile = path
          , optDoctrine = "Combined"
          , optTerm = "C.k(C.m(C.e,C.e))"
          , optFuel = 5
          , optPolicy = UseOnlyComputationalLR
          }
  result <- runCLI opts
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> do
      crCatExpr out @?= CatOp (OpName "C.e") []
      crValue out @?= VAtom "C.e"
      termSort (crNormalized out) @?= Sort (SortName "C.Obj") []
      assertBool "normalized differs from input" (crNormalized out /= crInputTerm out)
