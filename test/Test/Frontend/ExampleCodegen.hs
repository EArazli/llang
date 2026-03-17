{-# LANGUAGE OverloadedStrings #-}
module Test.Frontend.ExampleCodegen
  ( tests
  ) where

import Control.Exception (bracket)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Strat.CLI (parseArgs, runCLI)
import Strat.Frontend.Build (BuildResult(..), buildWithEnv, selectBuild)
import Strat.Frontend.Loader (loadModule)
import System.Directory
  ( createDirectory
  , doesFileExist
  , getTemporaryDirectory
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
    "Frontend.ExampleCodegen"
    [ testCase "logic_full_adder_codegen main emits structured JavaScript" testLogicFullAdderMain
    , testCase "logic_full_adder_codegen share shows reflected quote bindings" testLogicFullAdderShare
    , testCase "explicit_sharing_js_codegen main exposes reflected quotation IR" testExplicitSharingJsMain
    , testCase "pair-based autodiff share exposes reflected quotation IR" testPairAutodiffShare
    , testCase "CLI does not write FileTree outputs without --output" testCliNoOutputFlagSkipsWrites
    , testCase "CLI writes FileTree outputs with --output" testCliOutputFlagWrites
    ]

testLogicFullAdderMain :: Assertion
testLogicFullAdderMain = do
  result <- loadExampleBuild "examples/build/logic_full_adder_codegen.llang" "main"
  let out = brOutput result
  assertBool "expected halfAdder export" ("export const halfAdder = env => ({ sum:" `T.isInfixOf` out)
  assertBool "expected fullAdder export" ("export const fullAdder = env => ({ sum:" `T.isInfixOf` out)
  assertBool "expected xor emission" ("!==" `T.isInfixOf` out)
  assertBool "expected and emission" ("&&" `T.isInfixOf` out)
  assertBool "expected or emission" ("||" `T.isInfixOf` out)
  assertBool "expected cin lookup" ("env[\"cin\"]" `T.isInfixOf` out)

testLogicFullAdderShare :: Assertion
testLogicFullAdderShare = do
  result <- loadExampleBuild "examples/build/logic_full_adder_codegen.llang" "share"
  let out = brOutput result
  assertBool "expected reflected quote prologue" ("q_begin" `T.isInfixOf` out)
  assertBool "expected reflected var for a" ("q_var(\"a\"" `T.isInfixOf` out)
  assertBool "expected reflected var for b" ("q_var(\"b\"" `T.isInfixOf` out)
  assertBool "expected reflected xor binding" ("q_xor" `T.isInfixOf` out)
  assertBool "expected reflected and binding" ("q_and" `T.isInfixOf` out)
  assertBool "expected reflected quote epilogue" ("q_end" `T.isInfixOf` out)

testExplicitSharingJsMain :: Assertion
testExplicitSharingJsMain = do
  result <- loadExampleBuild "examples/build/explicit_sharing_js_codegen.llang" "main"
  let out = brOutput result
  assertBool "expected reflected quote prologue" ("q_begin" `T.isInfixOf` out)
  assertBool "expected reflected duplicate binding" ("q_dup" `T.isInfixOf` out)
  assertBool "expected reflected add binding" ("q_add" `T.isInfixOf` out)
  assertBool "expected reflected print binding" ("q_print" `T.isInfixOf` out)
  assertBool "expected reflected quote epilogue" ("q_end" `T.isInfixOf` out)
  assertBool "expected no old explicit-sharing bindings" (not ("let_" `T.isInfixOf` out || "res_" `T.isInfixOf` out || "returnRefs" `T.isInfixOf` out))

testPairAutodiffShare :: Assertion
testPairAutodiffShare = do
  result <- loadExampleBuild "examples/build/autodiff_times_sin_pair_core.llang" "share"
  let out = brOutput result
  assertBool "expected reflected quote prologue" ("q_begin" `T.isInfixOf` out)
  assertBool "expected reflected RefIds boundary encoding" ("refIds_cons" `T.isInfixOf` out)
  assertBool "expected reflected atomic RefId labels" ("refId_label" `T.isInfixOf` out)
  assertBool "expected reflected duplication nodes" ("q_dup" `T.isInfixOf` out)
  assertBool "expected reflected sine binding" ("q_sin" `T.isInfixOf` out)
  assertBool "expected reflected cosine binding" ("q_cos" `T.isInfixOf` out)
  assertBool "expected reflected multiplication binding" ("q_mul" `T.isInfixOf` out)
  assertBool "expected reflected quote epilogue" ("q_end" `T.isInfixOf` out)
  assertBool "expected no legacy WireIds encoding" (not ("wireIds_" `T.isInfixOf` out || "WireIds" `T.isInfixOf` out))
  assertBool "expected no explicit-sharing plumbing" (not ("let_" `T.isInfixOf` out || "res_" `T.isInfixOf` out || "returnRefs" `T.isInfixOf` out))

testCliNoOutputFlagSkipsWrites :: Assertion
testCliNoOutputFlagSkipsWrites =
  withFreshDirectory "llang-cli-no-output" $ \tmp -> do
    let outRoot = tmp </> "out"
    let program = tmp </> "jsartifact_filetree_hello.llang"
    TIO.writeFile program (jsArtifactProgram outRoot)
    opts <- require (parseArgs [program])
    out <- require =<< runCLI opts
    assertBool "expected emitted output to still be printed" ("main.mjs:" `T.isInfixOf` out)
    assertBool "expected emitted output to include JS body" ("console.log('hello');" `T.isInfixOf` out)
    fileExists <- doesFileExist (outRoot </> "main.mjs")
    assertBool "expected no file write without --output" (not fileExists)

testCliOutputFlagWrites :: Assertion
testCliOutputFlagWrites =
  withFreshDirectory "llang-cli-output" $ \tmp -> do
    let outRoot = tmp </> "out"
    let program = tmp </> "jsartifact_filetree_hello.llang"
    TIO.writeFile program (jsArtifactProgram outRoot)
    opts <- require (parseArgs [program, "--output"])
    _ <- require =<< runCLI opts
    let outFile = outRoot </> "main.mjs"
    fileExists <- doesFileExist outFile
    assertBool "expected file write with --output" fileExists
    body <- TIO.readFile outFile
    assertEqual "expected emitted file contents" "console.log('hello');" (T.strip body)

jsArtifactProgram :: FilePath -> T.Text
jsArtifactProgram outRoot =
  T.unlines
    [ "doctrine JSArtifact extends Artifact where {"
    , "  gen jsHello : [] -> [Doc] @Artifact;"
    , ""
    , "  rule computational jsHello_def -> : [] -> [Doc] @Artifact ="
    , "    jsHello == text(\"console.log('hello');\")"
    , "}"
    , ""
    , "module_surface JSArtifactUnit where {"
    , "  doctrine JSArtifact;"
    , "  mode Artifact;"
    , "}"
    , ""
    , "language JSArtifactLang where {"
    , "  doctrine JSArtifact;"
    , "  module_surface JSArtifactUnit;"
    , "}"
    , ""
    , "module Main in JSArtifactLang where {"
    , "  let main"
    , "  ---"
    , "  jsHello; singleFile(\"main.mjs\")"
    , "  ---"
    , "  export { main };"
    , "}"
    , ""
    , "pipeline main where {"
    , "  project export main;"
    , "  normalize { policy = \"computational_lr\"; fuel = 50; };"
    , "  emit via FileTree { root = \"" <> escapeLlangString (normalizeFilePath outRoot) <> "\" };"
    , "}"
    , ""
    , "build main from Main using main;"
    ]

normalizeFilePath :: FilePath -> FilePath
normalizeFilePath = map slash
  where
    slash '\\' = '/'
    slash c = c

escapeLlangString :: FilePath -> T.Text
escapeLlangString = T.concatMap escapeChar . T.pack
  where
    escapeChar '"' = "\\\""
    escapeChar '\\' = "\\\\"
    escapeChar c = T.singleton c

withFreshDirectory :: String -> (FilePath -> IO a) -> IO a
withFreshDirectory prefix action = bracket acquire cleanup action
  where
    acquire = do
      tmp <- getTemporaryDirectory
      (path, h) <- openTempFile tmp (prefix <> ".tmp")
      hClose h
      removeFile path
      createDirectory path
      pure path

    cleanup = removePathForcibly

loadExampleBuild :: FilePath -> T.Text -> IO BuildResult
loadExampleBuild path buildName = do
  env <- requireIO =<< loadModule path
  buildDef <- require (selectBuild env (Just buildName))
  require (buildWithEnv env buildDef)

require :: Either T.Text a -> IO a
require (Left err) = assertFailure (show err) >> fail "unreachable"
require (Right a) = pure a

requireIO :: Either T.Text a -> IO a
requireIO = require
