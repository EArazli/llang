{-# LANGUAGE OverloadedStrings #-}
module Test.Frontend.ExampleCodegen
  ( tests
  ) where

import Control.Exception (bracket)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Strat.CLI (parseArgs, runCLI)
import Strat.Frontend.Loader (loadModule)
import Strat.Frontend.Run (selectRun, runWithEnv, RunResult(..))
import System.Directory
  ( createDirectory
  , doesFileExist
  , getTemporaryDirectory
  , removeFile
  , removePathForcibly
  )
import System.FilePath ((</>))
import System.IO (hClose, openTempFile)


tests :: TestTree
tests =
  testGroup
    "Frontend.ExampleCodegen"
    [ testCase "logic_full_adder_codegen main emits structured JavaScript" testLogicFullAdderMain
    , testCase "logic_full_adder_codegen ssa shows attrs and producer links" testLogicFullAdderSsa
    , testCase "ssa_js_codegen main emits js-like SSA statements" testSsaJsMain
    , testCase "end-to-end autodiff example emits differentiated JavaScript" testEndToEndAutodiffMain
    , testCase "end-to-end autodiff core run exposes differentiated target IR" testEndToEndAutodiffCore
    , testCase "pair-based autodiff core stays in the source doctrine after one pass" testPairAutodiffCore
    , testCase "pair-based autodiff core stays closed after two passes" testPairAutodiffCore2
    , testCase "CLI does not write FileTree outputs without --output" testCliNoOutputFlagSkipsWrites
    , testCase "CLI writes FileTree outputs with --output" testCliOutputFlagWrites
    ]


testLogicFullAdderMain :: Assertion
testLogicFullAdderMain = do
  env <- requireIO =<< loadModule "examples/run/codegen/logic_full_adder_codegen.run.llang"
  runDef <- require (selectRun env (Just "main"))
  result <- require (runWithEnv env runDef)
  let out = prOutput result
  assertBool "expected halfAdder export" ("export const halfAdder = env => ({ sum:" `T.isInfixOf` out)
  assertBool "expected fullAdder export" ("export const fullAdder = env => ({ sum:" `T.isInfixOf` out)
  assertBool "expected xor emission" ("!==" `T.isInfixOf` out)
  assertBool "expected and emission" ("&&" `T.isInfixOf` out)
  assertBool "expected or emission" ("||" `T.isInfixOf` out)
  assertBool "expected cin lookup" ("env[\"cin\"]" `T.isInfixOf` out)

testLogicFullAdderSsa :: Assertion
testLogicFullAdderSsa = do
  env <- requireIO =<< loadModule "examples/run/codegen/logic_full_adder_codegen.run.llang"
  runDef <- require (selectRun env (Just "ssa"))
  result <- require (runWithEnv env runDef)
  let out = prOutput result
  assertBool "expected var attribute for a" ("attrs={s=\"a\"}" `T.isInfixOf` out)
  assertBool "expected var attribute for b" ("attrs={s=\"b\"}" `T.isInfixOf` out)
  assertBool "expected xor step" (" xor " `T.isInfixOf` out)
  assertBool "expected producer links in inputs" (" <- e" `T.isInfixOf` out)

testSsaJsMain :: Assertion
testSsaJsMain = do
  env <- requireIO =<< loadModule "examples/run/codegen/ssa_js_codegen.run.llang"
  runDef <- require (selectRun env (Just "main"))
  result <- require (runWithEnv env runDef)
  let out = prOutput result
  assertBool "expected const binding statements" ("const " `T.isInfixOf` out)
  assertBool "expected assignment in emitted code" (" = " `T.isInfixOf` out)
  assertBool "expected add operation call in emitted code" ("add(" `T.isInfixOf` out)
  assertBool "expected dup operation call in emitted code" ("dup(" `T.isInfixOf` out)
  assertBool "expected console.log statement" ("console.log(" `T.isInfixOf` out)
  assertBool "expected statement separators" (";\n" `T.isInfixOf` out)

testEndToEndAutodiffMain :: Assertion
testEndToEndAutodiffMain = do
  env <- requireIO =<< loadModule "examples/endtoend/autodiff_times_sin.run.llang"
  runDef <- require (selectRun env (Just "main"))
  result <- require (runWithEnv env runDef)
  let out = prOutput result
  assertBool "expected exported unary function block" ("export const timesSin = x => {" `T.isInfixOf` out)
  assertBool "expected shared tangent binding" ("const dx = { value: x, derivative: 1 };" `T.isInfixOf` out)
  assertBool "expected named product helper" ("const mulDual = (l, r) =>" `T.isInfixOf` out)
  assertBool "expected named sin helper" ("const sinDual = u =>" `T.isInfixOf` out)
  assertBool "expected product helper call in body" ("return mulDual(dx, sinDual(dx));" `T.isInfixOf` out)
  assertBool "expected reusable module without CLI side effect" (not ("console.log(" `T.isInfixOf` out))

testEndToEndAutodiffCore :: Assertion
testEndToEndAutodiffCore = do
  env <- requireIO =<< loadModule "examples/endtoend/autodiff_times_sin.run.llang"
  runDef <- require (selectRun env (Just "core"))
  result <- require (runWithEnv env runDef)
  let out = prOutput result
  assertBool "expected normalized dual constructor" ("mkDual" `T.isInfixOf` out)
  assertBool "expected normalized dual split" ("splitDual" `T.isInfixOf` out)
  assertBool "expected normalized cosine node" ("cosR" `T.isInfixOf` out)
  assertBool "expected normalized addition node" ("addR" `T.isInfixOf` out)
  assertBool "expected normalized multiplication node" ("mulR" `T.isInfixOf` out)
  assertBool "expected differentiated core to eliminate dsin" (not (" dsin " `T.isInfixOf` out))
  assertBool "expected differentiated core to eliminate dmul" (not (" dmul " `T.isInfixOf` out))

testPairAutodiffCore :: Assertion
testPairAutodiffCore = do
  env <- requireIO =<< loadModule "examples/endtoend/autodiff_times_sin_pair_core.run.llang"
  runDef <- require (selectRun env (Just "core"))
  result <- require (runWithEnv env runDef)
  let out = prOutput result
  assertBool "expected pair-valued arrow output" ("M.Arr(M.Pair(M.R, M.R), M.Pair(M.R, M.R))" `T.isInfixOf` out)
  assertBool "expected explicit pair constructor" (" mkPair " `T.isInfixOf` out)
  assertBool "expected explicit projection structure" (" fst " `T.isInfixOf` out)
  assertBool "expected explicit cosine node" (" cos " `T.isInfixOf` out)
  assertBool "expected explicit addition node" (" add " `T.isInfixOf` out)

testPairAutodiffCore2 :: Assertion
testPairAutodiffCore2 = do
  env <- requireIO =<< loadModule "examples/endtoend/autodiff_times_sin_pair_core.run.llang"
  runDef <- require (selectRun env (Just "core2"))
  result <- require (runWithEnv env runDef)
  let out = prOutput result
  assertBool "expected nested pair-valued arrow output" ("M.Arr(M.Pair(M.Pair(M.R, M.R), M.Pair(M.R, M.R))" `T.isInfixOf` out)
  assertBool "expected repeated pair constructors" (" mkPair " `T.isInfixOf` out)
  assertBool "expected sine nodes to remain in second-order core" (" sin " `T.isInfixOf` out)
  assertBool "expected cosine nodes to remain in second-order core" (" cos " `T.isInfixOf` out)
  assertBool "expected multiplication nodes in second-order core" (" mul " `T.isInfixOf` out)


testCliNoOutputFlagSkipsWrites :: Assertion
testCliNoOutputFlagSkipsWrites =
  withFreshDirectory "llang-cli-no-output" $ \tmp -> do
    let outRoot = tmp </> "out"
    let program = tmp </> "jsartifact_filetree_hello.run.llang"
    TIO.writeFile program (jsArtifactProgram outRoot)
    opts <- require (parseArgs [program])
    out <- require =<< runCLI opts
    assertBool "expected extracted output to still be printed" ("main.mjs:" `T.isInfixOf` out)
    assertBool "expected extracted output to include JS body" ("console.log('hello');" `T.isInfixOf` out)
    fileExists <- doesFileExist (outRoot </> "main.mjs")
    assertBool "expected no file write without --output" (not fileExists)


testCliOutputFlagWrites :: Assertion
testCliOutputFlagWrites =
  withFreshDirectory "llang-cli-output" $ \tmp -> do
    let outRoot = tmp </> "out"
    let program = tmp </> "jsartifact_filetree_hello.run.llang"
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
    , "    jsHello == text(s=\"console.log('hello');\")"
    , "}"
    , ""
    , "pipeline main where {"
    , "  normalize { policy = \"computational_lr\"; fuel = 50; };"
    , "  extract FileTree { root = \"" <> escapeLlangString (normalizeFilePath outRoot) <> "\" };"
    , "}"
    , ""
    , "run main using main where {"
    , "  source doctrine JSArtifact;"
    , "  source mode Artifact;"
    , "}"
    , "---"
    , "jsHello; singleFile(path=\"main.mjs\")"
    , "---"
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


require :: Either T.Text a -> IO a
require (Left err) = assertFailure (show err) >> fail "unreachable"
require (Right a) = pure a


requireIO :: Either T.Text a -> IO a
requireIO = require
