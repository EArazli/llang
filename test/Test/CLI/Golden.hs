{-# LANGUAGE OverloadedStrings #-}
module Test.CLI.Golden
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.CLI (runCLI, CLIOptions(..))
import Data.Text (Text)
import qualified Data.Text as T
import Paths_llang (getDataFileName)


tests :: TestTree
tests =
  testGroup
    "CLI.Golden"
    [ testCase "planar_monoid.run.llang output" (goldenRun "examples/poly/planar_monoid.run.llang" expectedPlanarMonoid)
    , testCase "cart_monoid.run.llang output" (goldenRun "examples/poly/cart_monoid.run.llang" expectedCartMonoid)
    ]


goldenRun :: FilePath -> Text -> Assertion
goldenRun relPath expected = do
  path <- getDataFileName relPath
  result <- runCLI (CLIOptions path Nothing)
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> out @?= expected

expectedPlanarMonoid :: Text
expectedPlanarMonoid =
  T.intercalate "\n"
    [ "normalized:"
    , "mode: M"
    , "in: []"
    , "out: [p0:A]"
    , "edges:"
    , "  e0: unit [] -> [p0]"
    ]

expectedCartMonoid :: Text
expectedCartMonoid =
  T.intercalate "\n"
    [ "normalized:"
    , "mode: M"
    , "in: [p0:A]"
    , "out: [p1:A]"
    , "edges:"
    , "  e0: dup [p0] -> [p2, p3]"
    , "  e1: mul [p2, p3] -> [p1]"
    ]
