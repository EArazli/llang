{-# LANGUAGE OverloadedStrings #-}
module Test.Frontend.ExamplesSmoke
  ( tests
  ) where

import Control.Monad (forM, forM_)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Text as T
import Data.List (isInfixOf, isSuffixOf, sort)
import Strat.Frontend.Build (buildWithEnv)
import Strat.Frontend.Env (meBuilds)
import Strat.Frontend.Loader (loadModule)
import System.Directory (doesDirectoryExist, listDirectory)
import System.FilePath ((</>))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit

tests :: TestTree
tests =
  testGroup
    "Frontend.ExamplesSmoke"
    [ testCase "all build examples execute" testAllBuildExamples
    , testCase "restored legacy-path examples execute" testAllLegacyExamples
    ]

testAllBuildExamples :: Assertion
testAllBuildExamples =
  runExampleRoots ["examples/build"]


testAllLegacyExamples :: Assertion
testAllLegacyExamples =
  runExampleRoots ["examples/run", "examples/endtoend"]


runExampleRoots :: [FilePath] -> Assertion
runExampleRoots roots = do
  files <- fmap concat (mapM collectFiles roots)
  let buildFiles =
        sort
          [ path
          | path <- files
          , ".llang" `isSuffixOf` path
          , not ("/xfail/" `isInfixOf` normalizePath path)
          ]
  assertBool "expected at least one example file" (not (null buildFiles))
  forM_ buildFiles $ \path -> do
    env <- requireIO =<< loadModule path
    let builds = M.toAscList (meBuilds env)
    assertBool ("expected at least one build in " <> path) (not (null builds))
    forM_ builds $ \(buildName, buildDef) ->
      if isSlowExampleBuild path buildName
        then pure ()
        else
          case buildWithEnv env buildDef of
            Left err ->
              assertFailure
                ( path
                    <> " --build "
                    <> T.unpack buildName
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

isSlowExampleBuild :: FilePath -> T.Text -> Bool
isSlowExampleBuild path buildName =
  S.member (normalizePath path, buildName) slowExampleBuilds

slowExampleBuilds :: S.Set (FilePath, T.Text)
slowExampleBuilds =
  S.fromList
    [ ("examples/build/autodiff_times_sin.llang", "main")
    , ("examples/build/autodiff_times_sin.llang", "main2")
    , ("examples/build/autodiff_times_sin_pair_core.llang", "main")
    , ("examples/build/autodiff_times_sin_pair_core.llang", "main2")
    , ("examples/build/autodiff_times_sin_pair_core.llang", "share2")
    , ("examples/endtoend/autodiff_times_sin.run.llang", "main")
    , ("examples/endtoend/autodiff_times_sin.run.llang", "main2")
    , ("examples/endtoend/autodiff_times_sin_pair_core.run.llang", "main")
    , ("examples/endtoend/autodiff_times_sin_pair_core.run.llang", "main2")
    , ("examples/run/dependent/path_identity.run.llang", "path_witness")
    , ("examples/run/dependent/path_identity.run.llang", "reversed_path")
    ]

requireIO :: Either T.Text a -> IO a
requireIO (Left err) = assertFailure (T.unpack err) >> fail "unreachable"
requireIO (Right a) = pure a
