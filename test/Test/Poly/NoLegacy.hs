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
  [ "examples/poly/planar_monoid.ssa.run.llang"
  , "examples/poly/cart_monoid.term.run.llang"
  , "examples/poly/stlc_bool.term.run.llang"
  , "examples/poly/peano.run.llang"
  , "examples/poly/ccc_surface/stlc.lam1.run.llang"
  , "examples/poly/implements_uses.run.llang"
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
