{-# LANGUAGE OverloadedStrings #-}
module Test.Value.Doc
  ( tests
  ) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit
import Data.Text (Text)
import qualified Data.Text as T
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
    , testCase "Doc extractor works for doctrines extending Doc" testExtendedDocExtraction
    , testCase "FileTree extractor works for doctrines extending Artifact" testExtendedArtifactFileTreeExtraction
    , testCase "Doc extractor rejects doctrines missing required generators" testDocExtractionMissingGenerator
    , testCase "Doc extractor rejects non-string text attribute sort" testDocExtractionWrongAttrKind
    , testCase "FileTree extractor rejects wrong singleFile signature" testFileTreeExtractionWrongSingleFileSig
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


testExtendedDocExtraction :: Assertion
testExtendedDocExtraction = do
  env <- require (elabDocProgram extendedDocProgram)
  runDef <- require (selectRun env (Just "main"))
  result <- require (runWithEnv env runDef)
  prOutput result @?= "(x)"


testExtendedArtifactFileTreeExtraction :: Assertion
testExtendedArtifactFileTreeExtraction = do
  env <- require (elabDocProgram extendedArtifactFileTreeProgram)
  runDef <- require (selectRun env (Just "main"))
  result <- require (runWithEnv env runDef)
  case prArtifact result of
    ArtExtracted _ files ->
      M.lookup "./out/main.mjs" files @?= Just "console.log('hello');"
    _ ->
      assertFailure "expected extracted FileTree artifact"


testDocExtractionMissingGenerator :: Assertion
testDocExtractionMissingGenerator = do
  env <- require (elabDocProgram missingCatProgram)
  runDef <- require (selectRun env (Just "main"))
  err <- requireLeft (runWithEnv env runDef)
  assertBool "expected missing cat diagnostic" ("pipeline: extract Doc: missing generator 'cat' in mode M" `T.isInfixOf` err)


testDocExtractionWrongAttrKind :: Assertion
testDocExtractionWrongAttrKind = do
  env <- require (elabDocProgram badTextAttrKindProgram)
  runDef <- require (selectRun env (Just "main"))
  err <- requireLeft (runWithEnv env runDef)
  assertBool "expected text attr literal kind diagnostic" ("pipeline: extract Doc: generator 'text' attribute 's' must have string literal kind" `T.isInfixOf` err)


testFileTreeExtractionWrongSingleFileSig :: Assertion
testFileTreeExtractionWrongSingleFileSig = do
  env <- require (elabDocProgram badSingleFileSigProgram)
  runDef <- require (selectRun env (Just "main"))
  err <- requireLeft (runWithEnv env runDef)
  assertBool "expected singleFile signature diagnostic" ("pipeline: extract FileTree: generator 'singleFile' has wrong signature; expected [Doc]->[FileTree] in mode M" `T.isInfixOf` err)


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


extendedDocProgram :: Text
extendedDocProgram =
  "doctrine PrettyDoc extends Doc where {\n"
    <> "  gen parens : [Doc] -> [Doc] @Doc;\n"
    <> "  rule computational parens_def -> : [Doc] -> [Doc] @Doc =\n"
    <> "    parens == (text(s=\"(\") * id[Doc]) ; cat ; (id[Doc] * text(s=\")\")) ; cat\n"
    <> "}\n"
    <> "pipeline p where {\n"
    <> "  normalize { policy = \"computational_lr\"; fuel = 50; };\n"
    <> "  extract Doc { stdout = true };\n"
    <> "}\n"
    <> "run main using p where {\n"
    <> "  source doctrine PrettyDoc;\n"
    <> "  source mode Doc;\n"
    <> "}\n"
    <> "---\n"
    <> "text(s=\"x\"); parens\n"
    <> "---\n"


extendedArtifactFileTreeProgram :: Text
extendedArtifactFileTreeProgram =
  "doctrine JSArtifact extends Artifact where {\n"
    <> "  gen jsHello : [] -> [Doc] @Artifact;\n"
    <> "  rule computational jsHello_def -> : [] -> [Doc] @Artifact =\n"
    <> "    jsHello == text(s=\"console.log('hello');\")\n"
    <> "}\n"
    <> "pipeline p where {\n"
    <> "  normalize { policy = \"computational_lr\"; fuel = 50; };\n"
    <> "  extract FileTree { root = \"./out\" };\n"
    <> "}\n"
    <> "run main using p where {\n"
    <> "  source doctrine JSArtifact;\n"
    <> "  source mode Artifact;\n"
    <> "}\n"
    <> "---\n"
    <> "jsHello; singleFile(path=\"main.mjs\")\n"
    <> "---\n"


missingCatProgram :: Text
missingCatProgram =
  "doctrine MissingCat where {\n"
    <> "  mode M acyclic classifiedBy M via M.U_M;\n"
    <> "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;\n"
    <> "  gen comp_var(a@M) : [a] -> [a] @M;\n"
    <> "  gen comp_reindex(a@M) : [a] -> [a] @M;\n"
    <> "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };\n"
    <> "  gen U_M : [] -> [M.U_M] @M;\n"
    <> "  attrsort Str = string;\n"
    <> "  attrsort Int = int;\n"
    <> "  gen Doc : [] -> [M.U_M] @M;\n"
    <> "  gen empty : [] -> [Doc] @M;\n"
    <> "  gen text { s:Str } : [] -> [Doc] @M;\n"
    <> "  gen line : [] -> [Doc] @M;\n"
    <> "  gen indent { n:Int } : [Doc] -> [Doc] @M;\n"
    <> "}\n"
    <> "pipeline p where {\n"
    <> "  extract Doc { stdout = true };\n"
    <> "}\n"
    <> "run main using p where {\n"
    <> "  source doctrine MissingCat;\n"
    <> "  source mode M;\n"
    <> "}\n"
    <> "---\n"
    <> "empty\n"
    <> "---\n"


badTextAttrKindProgram :: Text
badTextAttrKindProgram =
  "doctrine BadTextAttrKind where {\n"
    <> "  mode M acyclic classifiedBy M via M.U_M;\n"
    <> "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;\n"
    <> "  gen comp_var(a@M) : [a] -> [a] @M;\n"
    <> "  gen comp_reindex(a@M) : [a] -> [a] @M;\n"
    <> "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };\n"
    <> "  gen U_M : [] -> [M.U_M] @M;\n"
    <> "  attrsort Bad = int;\n"
    <> "  attrsort Int = int;\n"
    <> "  gen Doc : [] -> [M.U_M] @M;\n"
    <> "  gen empty : [] -> [Doc] @M;\n"
    <> "  gen text { s:Bad } : [] -> [Doc] @M;\n"
    <> "  gen line : [] -> [Doc] @M;\n"
    <> "  gen cat : [Doc, Doc] -> [Doc] @M;\n"
    <> "  gen indent { n:Int } : [Doc] -> [Doc] @M;\n"
    <> "}\n"
    <> "pipeline p where {\n"
    <> "  extract Doc { stdout = true };\n"
    <> "}\n"
    <> "run main using p where {\n"
    <> "  source doctrine BadTextAttrKind;\n"
    <> "  source mode M;\n"
    <> "}\n"
    <> "---\n"
    <> "empty\n"
    <> "---\n"


badSingleFileSigProgram :: Text
badSingleFileSigProgram =
  "doctrine BadSingleFileSig where {\n"
    <> "  mode M acyclic classifiedBy M via M.U_M;\n"
    <> "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;\n"
    <> "  gen comp_var(a@M) : [a] -> [a] @M;\n"
    <> "  gen comp_reindex(a@M) : [a] -> [a] @M;\n"
    <> "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };\n"
    <> "  gen U_M : [] -> [M.U_M] @M;\n"
    <> "  attrsort Str = string;\n"
    <> "  attrsort Int = int;\n"
    <> "  gen Doc : [] -> [M.U_M] @M;\n"
    <> "  gen FileTree : [] -> [M.U_M] @M;\n"
    <> "  gen empty : [] -> [Doc] @M;\n"
    <> "  gen text { s:Str } : [] -> [Doc] @M;\n"
    <> "  gen line : [] -> [Doc] @M;\n"
    <> "  gen cat : [Doc, Doc] -> [Doc] @M;\n"
    <> "  gen indent { n:Int } : [Doc] -> [Doc] @M;\n"
    <> "  gen singleFile { path:Str } : [] -> [FileTree] @M;\n"
    <> "  gen concatTree : [FileTree, FileTree] -> [FileTree] @M;\n"
    <> "}\n"
    <> "pipeline p where {\n"
    <> "  extract FileTree { root = \"./out\" };\n"
    <> "}\n"
    <> "run main using p where {\n"
    <> "  source doctrine BadSingleFileSig;\n"
    <> "  source mode M;\n"
    <> "}\n"
    <> "---\n"
    <> "singleFile(path=\"main.mjs\")\n"
    <> "---\n"


elabDocProgram :: Text -> Either Text ModuleEnv
elabDocProgram src = do
  raw <- parseRawFile src
  let baseEnv = emptyEnv { meDoctrines = preludeDoctrines }
  elabRawFileWithEnv baseEnv raw


require :: Either Text a -> IO a
require (Left err) = assertFailure (show err) >> fail "unreachable"
require (Right a) = pure a


requireLeft :: Either Text a -> IO Text
requireLeft (Left err) = pure err
requireLeft (Right _) = assertFailure "expected failure" >> fail "unreachable"
