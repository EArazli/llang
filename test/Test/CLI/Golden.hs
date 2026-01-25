{-# LANGUAGE OverloadedStrings #-}
module Test.CLI.Golden
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.Frontend.Run (runFile, rrOutput)
import Data.Text (Text)
import qualified Data.Text as T
import Paths_llang (getDataFileName)


tests :: TestTree
tests =
  testGroup
    "CLI.Golden"
    [ testCase "monoid.run.llang output" (goldenRun "examples/monoid.run.llang" expectedMonoid)
    , testCase "ccc.run.llang output" (goldenRun "examples/ccc.run.llang" expectedCCC)
    , testCase "stlc.run.llang output" (goldenRun "examples/ccc_surface/stlc.run.llang" expectedSTLC)
    ]


goldenRun :: FilePath -> Text -> Assertion
goldenRun relPath expected = do
  path <- getDataFileName relPath
  result <- runFile path Nothing
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> rrOutput out @?= expected

expectedMonoid :: Text
expectedMonoid =
  T.unlines
    [ "normalized: e"
    , "value: VString \"\""
    , "cat: CatOp (OpName \"Combined.e\") []"
    ]

expectedCCC :: Text
expectedCCC =
  T.unlines
    [ "normalized: CCC.f"
    , "value: VAtom \"CCC.f\""
    , "cat: CatOp (OpName \"CCC.f\") []"
    ]

expectedSTLC :: Text
expectedSTLC =
  T.unlines
    [ "normalized: CCC.T"
    , "value: VAtom \"CCC.T\""
    , "cat: CatOp (OpName \"CCC.T\") []"
    ]
