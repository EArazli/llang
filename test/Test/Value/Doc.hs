{-# LANGUAGE OverloadedStrings #-}
module Test.Value.Doc
  ( tests
  ) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit
import Data.Text (Text)
import qualified Data.Map.Strict as M
import Strat.DSL.Parse (parseRawFile)
import Strat.DSL.Elab (elabRawFileWithEnv)
import Strat.Frontend.Env (ModuleEnv, emptyEnv, meDoctrines)
import Strat.Frontend.Prelude (preludeDoctrines)
import Strat.Frontend.Run (selectRun, runWithEnv, RunResult(..), Artifact(..))


tests :: TestTree
tests =
  testGroup
    "Value.Doc"
    [ testCase "Doc extractor renders indent/cat/line" testDocExtraction
    , testCase "Artifact FileTree extractor renders embedded Doc content" testArtifactFileTreeExtraction
    ]


testDocExtraction :: Assertion
testDocExtraction = do
  env <- require (elabDocProgram docProgram)
  runDef <- require (selectRun env (Just "main"))
  result <- require (runWithEnv env runDef)
  prOutput result @?= "a\n  b"


testArtifactFileTreeExtraction :: Assertion
testArtifactFileTreeExtraction = do
  env <- require (elabDocProgram artifactFileTreeProgram)
  runDef <- require (selectRun env (Just "main"))
  result <- require (runWithEnv env runDef)
  case prArtifact result of
    ArtExtracted _ files ->
      M.lookup "./out/hello.txt" files @?= Just "hello"
    _ ->
      assertFailure "expected extracted FileTree artifact"


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


artifactFileTreeProgram :: Text
artifactFileTreeProgram =
  "pipeline p where {\n"
    <> "  extract FileTree { root = \"./out\" };\n"
    <> "}\n"
    <> "run main using p where {\n"
    <> "  source doctrine Artifact;\n"
    <> "  source mode Artifact;\n"
    <> "}\n"
    <> "---\n"
    <> "text(s=\"hello\"); singleFile(path=\"hello.txt\")\n"
    <> "---\n"


elabDocProgram :: Text -> Either Text ModuleEnv
elabDocProgram src = do
  raw <- parseRawFile src
  let baseEnv = emptyEnv { meDoctrines = preludeDoctrines }
  elabRawFileWithEnv baseEnv raw


require :: Either Text a -> IO a
require (Left err) = assertFailure (show err) >> fail "unreachable"
require (Right a) = pure a
