{-# LANGUAGE OverloadedStrings #-}
module Test.Frontend.ExampleCodegen
  ( tests
  ) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit
import qualified Data.Text as T
import Strat.Frontend.Loader (loadModule)
import Strat.Frontend.Run (selectRun, runWithEnv, RunResult(..))


tests :: TestTree
tests =
  testGroup
    "Frontend.ExampleCodegen"
    [ testCase "logic_full_adder_codegen main emits structured JavaScript" testLogicFullAdderMain
    , testCase "logic_full_adder_codegen ssa shows attrs and producer links" testLogicFullAdderSsa
    , testCase "ssa_js_codegen main emits js-like SSA statements" testSsaJsMain
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


require :: Either T.Text a -> IO a
require (Left err) = assertFailure (show err) >> fail "unreachable"
require (Right a) = pure a


requireIO :: Either T.Text a -> IO a
requireIO = require
