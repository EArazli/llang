{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.StdlibCoherence
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Control.Exception (evaluate)
import System.Timeout (timeout)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import Strat.Frontend.Loader (loadModule)
import Strat.Frontend.Env (mePolyDoctrines)
import Strat.Poly.Coherence (checkCoherence)
import Strat.Poly.CriticalPairs (CPMode(..))
import Strat.Kernel.RewriteSystem (RewritePolicy(..))
import Strat.Poly.Doctrine (Doctrine)
import Paths_llang (getDataFileName)


tests :: TestTree
tests =
  testGroup
    "Poly.Stdlib"
    [ testCase "coherence on cart_monoid has no obligations" testStdlibCoherence
    , testCase "coherence check terminates quickly" testCoherenceTimeout
    ]

require :: Either Text a -> IO a
require = either (assertFailure . T.unpack) pure

lookupDoc :: Text -> M.Map Text Doctrine -> IO Doctrine
lookupDoc name docs =
  case M.lookup name docs of
    Nothing -> assertFailure ("missing doctrine " <> T.unpack name)
    Just doc -> pure doc


testStdlibCoherence :: Assertion
testStdlibCoherence = do
  path <- getDataFileName "examples/poly/cart_monoid.poly.llang"
  env <- require =<< loadModule path
  assertBool "expected StructCartesian loaded" (M.member "StructCartesian" (mePolyDoctrines env))
  doc <- lookupDoc "CartMonoid" (mePolyDoctrines env)
  res <- require (checkCoherence CP_StructuralVsComputational UseAllOriented 4 doc)
  assertBool "expected no obligations" (null res)


testCoherenceTimeout :: Assertion
testCoherenceTimeout = do
  path <- getDataFileName "examples/poly/coherence_demo.poly.llang"
  env <- require =<< loadModule path
  doc <- lookupDoc "CoherenceDemo" (mePolyDoctrines env)
  let action =
        evaluate $
          case checkCoherence CP_StructuralVsComputational UseAllOriented 2 doc of
            Left err -> Left err
            Right results -> Right (length results)
  timed <- timeout (2 * 1000 * 1000) action
  case timed of
    Nothing -> assertFailure "coherence check timed out"
    Just (Left err) -> assertFailure (T.unpack err)
    Just (Right count) -> count @?= 1
