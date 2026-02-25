{-# LANGUAGE OverloadedStrings #-}
module Test.Frontend.StdlibIntegration
  ( tests
  ) where

import Control.Monad (forM, forM_)
import Data.List (isSuffixOf, sort)
import qualified Data.Map.Strict as M
import qualified Data.Text as T
import System.Directory (doesDirectoryExist, listDirectory)
import System.FilePath ((</>))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit

import Strat.Frontend.Env (meDoctrines)
import Strat.Frontend.Loader (loadModule)


tests :: TestTree
tests =
  testGroup
    "Frontend.StdlibIntegration"
    [ testCase "all stdlib files parse and elaborate" testAllStdlibFilesLoad
    , testCase "functor applications compose in combined effects library" testCombinedEffectsFunctorApply
    , testCase "template file with multiple apply declarations elaborates" testStateTemplateApplies
    ]


testAllStdlibFilesLoad :: Assertion
testAllStdlibFilesLoad = do
  files <- collectFiles "stdlib"
  let stdlibFiles =
        sort
          [ path
          | path <- files
          , ".llang" `isSuffixOf` path
          ]
  assertBool "expected at least one stdlib file" (not (null stdlibFiles))
  forM_ stdlibFiles $ \path -> do
    _ <- requireIO =<< loadModule path
    pure ()


testCombinedEffectsFunctorApply :: Assertion
testCombinedEffectsFunctorApply = do
  env <- requireIO =<< loadModule "examples/lib/effects/combined.llang"
  let docs = meDoctrines env
  assertBool "expected ExnE doctrine from apply Exception" (M.member "ExnE" docs)
  assertBool "expected WriterW doctrine from apply Writer" (M.member "WriterW" docs)
  assertBool "expected Combined doctrine from effects composition" (M.member "Combined" docs)
  assertBool "expected CombinedOut doctrine extension" (M.member "CombinedOut" docs)


testStateTemplateApplies :: Assertion
testStateTemplateApplies = do
  env <- requireIO =<< loadModule "examples/lib/templates/state.template.llang"
  let docs = meDoctrines env
  assertBool "expected StateNat doctrine from first apply" (M.member "StateNat" docs)
  assertBool "expected StateBool doctrine from second apply" (M.member "StateBool" docs)


collectFiles :: FilePath -> IO [FilePath]
collectFiles dir = do
  entries <- listDirectory dir
  fmap concat $ forM (sort entries) $ \entry -> do
    let path = dir </> entry
    isDir <- doesDirectoryExist path
    if isDir
      then collectFiles path
      else pure [path]


requireIO :: Either T.Text a -> IO a
requireIO (Left err) = assertFailure (T.unpack err) >> fail "unreachable"
requireIO (Right a) = pure a
