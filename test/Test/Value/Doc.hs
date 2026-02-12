{-# LANGUAGE OverloadedStrings #-}
module Test.Value.Doc
  ( tests
  ) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit
import Data.Text (Text)
import Strat.DSL.Parse (parseRawFile)
import Strat.DSL.Elab (elabRawFileWithEnv)
import Strat.Frontend.Env (ModuleEnv, emptyEnv, meDoctrines)
import Strat.Frontend.Prelude (preludeDoctrines)
import Strat.Frontend.Run (selectRun, runWithEnv, RunResult(..))


tests :: TestTree
tests =
  testGroup
    "Value.Doc"
    [ testCase "Doc extractor renders indent/cat/line" testDocExtraction
    ]


testDocExtraction :: Assertion
testDocExtraction = do
  env <- require (elabDocProgram docProgram)
  runDef <- require (selectRun env (Just "main"))
  result <- require (runWithEnv env runDef)
  prOutput result @?= "a\n  b"


docProgram :: Text
docProgram =
  "pipeline p where {\n"
    <> "  extract Doc { stdout = true };\n"
    <> "}\n"
    <> "run main using p where {\n"
    <> "  source doctrine Doc;\n"
    <> "  source mode Doc;\n"
    <> "}\n"
    <> "---\n"
    <> "text(s=\"a\") * (line * text(s=\"b\"); cat); cat; indent(n=2)\n"
    <> "---\n"


elabDocProgram :: Text -> Either Text ModuleEnv
elabDocProgram src = do
  raw <- parseRawFile src
  let baseEnv = emptyEnv { meDoctrines = preludeDoctrines }
  elabRawFileWithEnv baseEnv raw


require :: Either Text a -> IO a
require (Left err) = assertFailure (show err) >> fail "unreachable"
require (Right a) = pure a
