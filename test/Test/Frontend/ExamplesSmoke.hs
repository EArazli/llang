{-# LANGUAGE OverloadedStrings #-}
module Test.Frontend.ExamplesSmoke
  ( tests
  ) where

import Control.Monad (forM, forM_)
import Data.List (isInfixOf, isSuffixOf, sort)
import qualified Data.Map.Strict as M
import qualified Data.Text as T
import System.Directory (doesDirectoryExist, listDirectory)
import System.FilePath ((</>))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit

import Strat.Frontend.Env (meRuns)
import Strat.Frontend.Loader (loadModule)
import Strat.Frontend.Run (runWithEnv)


tests :: TestTree
tests =
  testGroup
    "Frontend.ExamplesSmoke"
    [ testCase "all non-xfail runnable examples execute" testAllRunExamples
    ]


testAllRunExamples :: Assertion
testAllRunExamples = do
  files <- collectFiles "examples/run"
  let runFiles =
        sort
          [ path
          | path <- files
          , ".run.llang" `isSuffixOf` path
          , not ("/xfail/" `isInfixOf` normalizePath path)
          ]
  assertBool "expected at least one run file" (not (null runFiles))
  forM_ runFiles $ \path -> do
    env <- requireIO =<< loadModule path
    let runs = M.toAscList (meRuns env)
    assertBool ("expected at least one run in " <> path) (not (null runs))
    forM_ runs $ \(runName, runDef) ->
      case runWithEnv env runDef of
        Left err ->
          assertFailure
            ( path
                <> " --run "
                <> T.unpack runName
                <> " failed:\n"
                <> T.unpack err
            )
        Right _ ->
          pure ()


collectFiles :: FilePath -> IO [FilePath]
collectFiles dir = do
  entries <- listDirectory dir
  fmap concat $ forM (sort entries) $ \entry -> do
    let path = dir </> entry
    isDir <- doesDirectoryExist path
    if isDir
      then collectFiles path
      else pure [path]


normalizePath :: FilePath -> FilePath
normalizePath = map slash
  where
    slash '\\' = '/'
    slash c = c


requireIO :: Either T.Text a -> IO a
requireIO (Left err) = assertFailure (T.unpack err) >> fail "unreachable"
requireIO (Right a) = pure a
