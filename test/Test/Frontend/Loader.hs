{-# LANGUAGE OverloadedStrings #-}
module Test.Frontend.Loader
  ( tests
  ) where

import Control.Exception (bracket)
import qualified Data.Map.Strict as M
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Strat.Frontend.Env (meBuilds, meModules, meProofStats, proofStatsTotal)
import Strat.Frontend.Loader
  ( CacheStatus(..)
  , CompilationUnit(..)
  , CompilationUnitArtifacts(..)
  , LoadedProject(..)
  , loadProject
  )
import System.Directory
  ( canonicalizePath
  , createDirectory
  , doesDirectoryExist
  , getTemporaryDirectory
  , listDirectory
  , removeFile
  , removePathForcibly
  )
import System.FilePath ((</>))
import System.IO (hClose, openTempFile)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit


tests :: TestTree
tests =
  testGroup
    "Frontend.Loader"
    [ testCase "loadProject records explicit compilation units and direct imports" testLoadProjectUnits
    , testCase "loadProject reuses persisted compilation units on a second load" testLoadProjectCacheHits
    , testCase "loadProject stores cache entries under the compiler fingerprint namespace" testLoadProjectCompilerFingerprintNamespace
    , testCase "loadProject reports missing files with a structured error" testLoadProjectMissingFile
    , testCase "loadProject does not double-count proof stats for duplicate equal units" testLoadProjectProofStatsDeduped
    ]


testLoadProjectUnits :: Assertion
testLoadProjectUnits =
  withTempDir "llang-loader" $ \dir -> do
    let libPath = dir </> "lib.llang"
        midPath = dir </> "mid.llang"
        mainPath = dir </> "main.llang"
    TIO.writeFile libPath libProgram
    TIO.writeFile midPath midProgram
    TIO.writeFile mainPath mainProgram
    absLib <- canonicalizePath libPath
    absMid <- canonicalizePath midPath
    absMain <- canonicalizePath mainPath
    project <- requireIO =<< loadProject mainPath
    M.size (lpUnits project) @?= 3
    let units = lpUnits project
    case M.lookup absMain units of
      Nothing -> assertFailure "expected main compilation unit"
      Just unit -> cuImports unit @?= [absMid]
    case M.lookup absMid units of
      Nothing -> assertFailure "expected mid compilation unit"
      Just unit -> do
        cuImports unit @?= [absLib]
        assertBool "expected explicit compiled declarations in mid unit" (not (null (cuaDecls (cuArtifacts unit))))
        assertBool "expected App module in mid unit artifacts" (M.member "App" (cuaModules (cuArtifacts unit)))
        assertBool "expected main build in mid unit artifacts" (M.member "main" (cuaBuilds (cuArtifacts unit)))
    case M.lookup absLib units of
      Nothing -> assertFailure "expected lib compilation unit"
      Just unit -> do
        cuImports unit @?= []
        assertBool "expected Greeting module in lib unit artifacts" (M.member "Greeting" (cuaModules (cuArtifacts unit)))
    assertBool "expected Greeting module from imported unit" (M.member "Greeting" (meModules (lpEnv project)))
    assertBool "expected App module from mid unit" (M.member "App" (meModules (lpEnv project)))
    assertBool "expected build from imported unit" (M.member "main" (meBuilds (lpEnv project)))


testLoadProjectCacheHits :: Assertion
testLoadProjectCacheHits =
  withTempDir "llang-loader-cache" $ \dir -> do
    let libPath = dir </> "lib.llang"
        midPath = dir </> "mid.llang"
        mainPath = dir </> "main.llang"
    TIO.writeFile libPath libProgram
    TIO.writeFile midPath midProgram
    TIO.writeFile mainPath mainProgram
    project1 <- requireIO =<< loadProject mainPath
    assertBool "expected initial elaboration misses" (all ((== CacheMiss) . cuCacheStatus) (M.elems (lpUnits project1)))
    project2 <- requireIO =<< loadProject mainPath
    assertBool "expected second load to use persisted cache" (all ((== CacheHit) . cuCacheStatus) (M.elems (lpUnits project2)))


testLoadProjectCompilerFingerprintNamespace :: Assertion
testLoadProjectCompilerFingerprintNamespace =
  withTempDir "llang-loader-fingerprint" $ \dir -> do
    let libPath = dir </> "lib.llang"
        midPath = dir </> "mid.llang"
        mainPath = dir </> "main.llang"
        cacheRoot = dir </> ".llang-cache"
    TIO.writeFile libPath libProgram
    TIO.writeFile midPath midProgram
    TIO.writeFile mainPath mainProgram
    _ <- requireIO =<< loadProject mainPath
    rootExists <- doesDirectoryExist cacheRoot
    assertBool "expected cache root" rootExists
    cacheNamespaces <- listDirectory cacheRoot
    assertBool "expected a namespaced compiler cache directory" (length cacheNamespaces == 1)
    case cacheNamespaces of
      [namespaceDir] -> do
        let cacheDir = cacheRoot </> namespaceDir </> "units"
        exists <- doesDirectoryExist cacheDir
        assertBool "expected compiler-fingerprint cache units directory" exists
        cacheEntries <- listDirectory cacheDir
        assertBool "expected compiler-fingerprint cache files" (not (null cacheEntries))
      _ -> assertFailure "unreachable"


testLoadProjectMissingFile :: Assertion
testLoadProjectMissingFile =
  withTempDir "llang-loader-missing" $ \dir -> do
    let missingPath = dir </> "missing.llang"
    result <- loadProject missingPath
    case result of
      Left err ->
        assertBool
          ("expected structured read failure, got: " <> T.unpack err)
          ("failed to read" `T.isInfixOf` err || "failed to resolve path" `T.isInfixOf` err)
      Right _ ->
        assertFailure "expected missing file to return a structured loader error"


testLoadProjectProofStatsDeduped :: Assertion
testLoadProjectProofStatsDeduped =
  withTempDir "llang-loader-proof-stats" $ \dir -> do
    sample <- TIO.readFile "examples/build/autodiff_times_sin_pair_core.llang"
    let lib1Path = dir </> "lib1.llang"
        lib2Path = dir </> "lib2.llang"
        mainPath = dir </> "main.llang"
    TIO.writeFile lib1Path sample
    TIO.writeFile lib2Path sample
    TIO.writeFile
      mainPath
      ( T.unlines
          [ "include \"lib1.llang\";"
          , "include \"lib2.llang\";"
          ]
      )
    projectSingle <- requireIO =<< loadProject lib1Path
    projectDup <- requireIO =<< loadProject mainPath
    let singleProofs = proofStatsTotal (meProofStats (lpEnv projectSingle))
        dupProofs = proofStatsTotal (meProofStats (lpEnv projectDup))
    assertBool "expected sample project to contribute proof stats" (singleProofs > 0)
    dupProofs @?= singleProofs


libProgram :: T.Text
libProgram =
  T.unlines
    [ "module_surface DocUnit where {"
    , "  doctrine Doc;"
    , "  mode Doc;"
    , "}"
    , "language DocLang where {"
    , "  doctrine Doc;"
    , "  module_surface DocUnit;"
    , "}"
    , "module Greeting in DocLang where {"
    , "  let hello"
    , "  ---"
    , "  text(\"hello\")"
    , "  ---"
    , "  export { hello };"
    , "}"
    ]


midProgram :: T.Text
midProgram =
  T.unlines
    [ "include \"lib.llang\";"
    , "module App in DocLang where {"
    , "  import Greeting as Lib;"
    , "  let main"
    , "  ---"
    , "  Lib::hello"
    , "  ---"
    , "  export { main };"
    , "}"
    , "pipeline p where {"
    , "  emit via Doc { stdout = true; };"
    , "}"
    , "build main from App using p;"
    ]


mainProgram :: T.Text
mainProgram =
  T.unlines
    [ "include \"mid.llang\";"
    ]


withTempDir :: String -> (FilePath -> IO a) -> IO a
withTempDir prefix action = do
  tmp <- getTemporaryDirectory
  bracket
    (do
        (path, handle) <- openTempFile tmp prefix
        hClose handle
        removeFile path
        createDirectory path
        pure path
    )
    removePathForcibly
    action


requireIO :: Either T.Text a -> IO a
requireIO (Left err) = assertFailure (T.unpack err) >> fail "unreachable"
requireIO (Right x) = pure x
