{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.NoLegacy
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Control.Monad (forM_)
import qualified Data.Text as T
import Strat.CLI (runCLI, CLIOptions(..))
import Paths_llang (getDataFileName)


tests :: TestTree
tests =
  testGroup
    "Poly.NoLegacy"
    [ testCase "poly examples run without legacy surfaces" testNoLegacyExamples
    ]


polyExamples :: [FilePath]
polyExamples =
  [ "examples/run/surfaces/planar_monoid.ssa.run.llang"
  , "examples/run/terms/cart_monoid.term.run.llang"
  , "examples/run/terms/stlc_bool.term.run.llang"
  , "examples/run/algebra/peano.run.llang"
  , "examples/run/surfaces/implements_uses.run.llang"
  , "examples/dependent/vec.llang"
  , "examples/dependent/lambda_beta.llang"
  ]


testNoLegacyExamples :: Assertion
testNoLegacyExamples =
  forM_ polyExamples $ \relPath -> do
    path <- getDataFileName relPath
    result <- runCLI (CLIOptions path Nothing)
    case result of
      Left err ->
        assertFailure ("expected success for " <> relPath <> ": " <> T.unpack err)
      Right _ -> pure ()
