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
    , testCase "logic_full_adder_codegen share shows quoted bindings and attrs" testLogicFullAdderShare
    , testCase "explicit_sharing_js_codegen main exposes mixed quoted bindings" testExplicitSharingJsMain
    , testCase "end-to-end autodiff example emits differentiated JavaScript" testEndToEndAutodiffMain
    , testCase "end-to-end autodiff core run exposes differentiated target IR" testEndToEndAutodiffCore
    , testCase "pair-based autodiff main exposes quoted explicit-sharing IR" testPairAutodiffMain
    , testCase "pair-based autodiff main2 exposes quoted second-order IR" testPairAutodiffMain2
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

testLogicFullAdderShare :: Assertion
testLogicFullAdderShare = do
  env <- requireIO =<< loadModule "examples/run/codegen/logic_full_adder_codegen.run.llang"
  runDef <- require (selectRun env (Just "share"))
  result <- require (runWithEnv env runDef)
  let out = prOutput result
  assertBool "expected residual var for a" ("res_var(s=\"a\")" `T.isInfixOf` out)
  assertBool "expected residual var for b" ("res_var(s=\"b\")" `T.isInfixOf` out)
  assertBool "expected residual xor binding" ("res_xor" `T.isInfixOf` out)
  assertBool "expected residual and binding" ("res_and" `T.isInfixOf` out)

testExplicitSharingJsMain :: Assertion
testExplicitSharingJsMain = do
  env <- requireIO =<< loadModule "examples/run/codegen/explicit_sharing_js_codegen.run.llang"
  runDef <- require (selectRun env (Just "main"))
  result <- require (runWithEnv env runDef)
  let out = prOutput result
  assertBool "expected explicit-sharing program output" ("M.Prog(" `T.isInfixOf` out)
  assertBool "expected shared duplicate binding" ("let_dup" `T.isInfixOf` out)
  assertBool "expected residual add binding" ("res_add" `T.isInfixOf` out)
  assertBool "expected residual print binding" ("res_print" `T.isInfixOf` out)
  assertBool "expected quote bundle plumbing" ("returnRefs" `T.isInfixOf` out)
  assertBool "expected no old naming attrsorts" (not ("__quote_str" `T.isInfixOf` out))

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

testPairAutodiffMain :: Assertion
testPairAutodiffMain = do
  env <- requireIO =<< loadModule "examples/endtoend/autodiff_times_sin_pair_core.run.llang"
  runDef <- require (selectRun env (Just "main"))
  result <- require (runWithEnv env runDef)
  let out = prOutput result
  assertBool "expected quoted program output" ("M.Prog(" `T.isInfixOf` out)
  assertBool "expected residual duplication nodes" ("res_dup" `T.isInfixOf` out)
  assertBool "expected shared sine binding" ("let_sin" `T.isInfixOf` out)
  assertBool "expected shared cosine binding" ("let_cos" `T.isInfixOf` out)
  assertBool "expected shared multiplication binding" ("let_mul" `T.isInfixOf` out)
  assertBool "expected quoted program terminator" ("returnRefs" `T.isInfixOf` out)
  assertBool "expected no legacy quote-name sort" (not ("__quote_str" `T.isInfixOf` out))

testPairAutodiffMain2 :: Assertion
testPairAutodiffMain2 = do
  env <- requireIO =<< loadModule "examples/endtoend/autodiff_times_sin_pair_core.run.llang"
  runDef <- require (selectRun env (Just "main2"))
  result <- require (runWithEnv env runDef)
  let out = prOutput result
  assertBool "expected quoted program output" ("M.Prog(" `T.isInfixOf` out)
  assertBool "expected second-order pair input type" ("M.Pair(M.Pair(M.R, M.R), M.Pair(M.R, M.R))" `T.isInfixOf` out)
  assertBool "expected residual duplication nodes" ("res_dup" `T.isInfixOf` out)
  assertBool "expected shared sine binding" ("let_sin" `T.isInfixOf` out)
  assertBool "expected shared cosine binding" ("let_cos" `T.isInfixOf` out)
  assertBool "expected shared addition binding" ("let_add" `T.isInfixOf` out)
  assertBool "expected quoted program terminator" ("returnRefs" `T.isInfixOf` out)
  assertBool "expected no legacy quote-name sort" (not ("__quote_str" `T.isInfixOf` out))


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
