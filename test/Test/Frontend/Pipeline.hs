{-# LANGUAGE OverloadedStrings #-}
module Test.Frontend.Pipeline
  ( tests
  ) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit
import Data.Text (Text)
import qualified Data.Text as T
import Strat.DSL.Parse (parseRawFile)
import Strat.DSL.Elab (elabRawFileWithEnv)
import Strat.Frontend.Env (ModuleEnv, emptyEnv, meDoctrines)
import Strat.Frontend.Prelude (preludeDoctrines)
import Strat.Frontend.Run (selectRun, runWithEnv, RunResult(..))


tests :: TestTree
tests =
  testGroup
    "Frontend.Pipeline"
    [ testCase "pipeline foliate + forget roundtrip smoke" testPipelineRoundtrip
    ]


testPipelineRoundtrip :: Assertion
testPipelineRoundtrip = do
  env <- require (elabProgram program)
  runDef <- require (selectRun env (Just "main"))
  result <- require (runWithEnv env runDef)
  assertBool "expected diagram output" ("edges:" `T.isInfixOf` prOutput result)


program :: Text
program =
  "doctrine D where {\n"
    <> "  mode M acyclic;\n"
    <> "  type T @M;\n"
    <> "  gen a : [] -> [T] @M;\n"
    <> "  gen b : [T] -> [T] @M;\n"
    <> "}\n"
    <> "derived doctrine D_SSA = foliated D mode M with {\n"
    <> "  policy = \"stable_edge_id\";\n"
    <> "  naming = \"boundary_labels_first\";\n"
    <> "};\n"
    <> "pipeline p where {\n"
    <> "  extract foliate into D_SSA;\n"
    <> "  apply D_SSA.forget;\n"
    <> "  extract diagram;\n"
    <> "}\n"
    <> "run main using p where {\n"
    <> "  source doctrine D;\n"
    <> "  source mode M;\n"
    <> "}\n"
    <> "---\n"
    <> "a; b\n"
    <> "---\n"


elabProgram :: Text -> Either Text ModuleEnv
elabProgram src = do
  raw <- parseRawFile src
  let baseEnv = emptyEnv { meDoctrines = preludeDoctrines }
  elabRawFileWithEnv baseEnv raw


require :: Either Text a -> IO a
require (Left err) = assertFailure (show err) >> fail "unreachable"
require (Right a) = pure a
