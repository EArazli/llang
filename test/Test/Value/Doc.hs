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
    , testCase "Doc extractor ignores builtin parameter names" testDocExtractionIgnoresBuiltinParamNames
    , testCase "Doc extractor rejects doctrines missing required generators" testDocExtractionMissingGenerator
    , testCase "Doc extractor rejects non-string text literal type" testDocExtractionWrongLiteralKind
    , testCase "Doc extractor rejects text with extra term parameters" testDocExtractionExtraTextParam
    , testCase "Doc extractor rejects indent with non-int literal type" testDocExtractionWrongIndentLiteralKind
    , testCase "FileTree extractor rejects wrong singleFile signature" testFileTreeExtractionWrongSingleFileSig
    , testCase "FileTree extractor rejects singleFile with extra term parameters" testFileTreeExtractionExtraSingleFileParam
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


testDocExtractionIgnoresBuiltinParamNames :: Assertion
testDocExtractionIgnoresBuiltinParamNames = do
  env <- require (elabDocProgram renamedBuiltinParamProgram)
  runDef <- require (selectRun env (Just "main"))
  result <- require (runWithEnv env runDef)
  prOutput result @?= "a\n  b"


testDocExtractionMissingGenerator :: Assertion
testDocExtractionMissingGenerator = do
  env <- require (elabDocProgram missingCatProgram)
  runDef <- require (selectRun env (Just "main"))
  err <- requireLeft (runWithEnv env runDef)
  assertBool "expected missing cat diagnostic" ("pipeline: extract Doc: missing generator 'cat' in mode M" `T.isInfixOf` err)


testDocExtractionWrongLiteralKind :: Assertion
testDocExtractionWrongLiteralKind = do
  env <- require (elabDocProgram badTextLiteralKindProgram)
  runDef <- require (selectRun env (Just "main"))
  err <- requireLeft (runWithEnv env runDef)
  assertBool "expected text parameter literal kind diagnostic" ("pipeline: extract Doc: generator 'text' sole term parameter must admit string literals" `T.isInfixOf` err)


testDocExtractionExtraTextParam :: Assertion
testDocExtractionExtraTextParam = do
  env <- require (elabDocProgram badTextExtraParamProgram)
  runDef <- require (selectRun env (Just "main"))
  err <- requireLeft (runWithEnv env runDef)
  assertBool "expected text arity diagnostic" ("pipeline: extract Doc: generator 'text' must have exactly one sole term parameter" `T.isInfixOf` err)


testDocExtractionWrongIndentLiteralKind :: Assertion
testDocExtractionWrongIndentLiteralKind = do
  env <- require (elabDocProgram badIndentLiteralKindProgram)
  runDef <- require (selectRun env (Just "main"))
  err <- requireLeft (runWithEnv env runDef)
  assertBool "expected indent parameter literal kind diagnostic" ("pipeline: extract Doc: generator 'indent' sole term parameter must admit int literals" `T.isInfixOf` err)


testFileTreeExtractionWrongSingleFileSig :: Assertion
testFileTreeExtractionWrongSingleFileSig = do
  env <- require (elabDocProgram badSingleFileSigProgram)
  runDef <- require (selectRun env (Just "main"))
  err <- requireLeft (runWithEnv env runDef)
  assertBool "expected singleFile signature diagnostic" ("pipeline: extract FileTree: generator 'singleFile' has wrong signature; expected [Doc]->[FileTree] in mode M" `T.isInfixOf` err)


testFileTreeExtractionExtraSingleFileParam :: Assertion
testFileTreeExtractionExtraSingleFileParam = do
  env <- require (elabDocProgram badSingleFileExtraParamProgram)
  runDef <- require (selectRun env (Just "main"))
  err <- requireLeft (runWithEnv env runDef)
  assertBool "expected singleFile arity diagnostic" ("pipeline: extract FileTree: generator 'singleFile' must have exactly one sole term parameter" `T.isInfixOf` err)


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
    <> "text(\"a\") * (line * text(\"b\"); cat); cat; indent(2)\n"
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
    <> "text(\"hello\"); singleFile(\"hello.txt\")\n"
    <> "---\n"


extendedDocProgram :: Text
extendedDocProgram =
  "doctrine PrettyDoc extends Doc where {\n"
    <> "  gen parens : [Doc] -> [Doc] @Doc;\n"
    <> "  rule computational parens_def -> : [Doc] -> [Doc] @Doc =\n"
    <> "    parens == (text(\"(\") * id[Doc]) ; cat ; (id[Doc] * text(\")\")) ; cat\n"
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
    <> "text(\"x\"); parens\n"
    <> "---\n"


extendedArtifactFileTreeProgram :: Text
extendedArtifactFileTreeProgram =
  "doctrine JSArtifact extends Artifact where {\n"
    <> "  gen jsHello : [] -> [Doc] @Artifact;\n"
    <> "  rule computational jsHello_def -> : [] -> [Doc] @Artifact =\n"
    <> "    jsHello == text(\"console.log('hello');\")\n"
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
    <> "jsHello; singleFile(\"main.mjs\")\n"
    <> "---\n"


renamedBuiltinParamProgram :: Text
renamedBuiltinParamProgram =
  "doctrine RenamedBuiltinParams where {\n"
    <> "  mode M acyclic classifiedBy M via M.U_M;\n"
    <> "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;\n"
    <> "  gen comp_var(a@M) : [a] -> [a] @M;\n"
    <> "  gen comp_reindex(a@M) : [a] -> [a] @M;\n"
    <> "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };\n"
    <> "  gen U_M : [] -> [M.U_M] @M;\n"
    <> "  gen Str : [] -> [M.U_M] @M;\n"
    <> "  literal Str @M = string;\n"
    <> "  gen Int : [] -> [M.U_M] @M;\n"
    <> "  literal Int @M = int;\n"
    <> "  gen Doc : [] -> [M.U_M] @M;\n"
    <> "  gen empty : [] -> [Doc] @M;\n"
    <> "  gen text(payload:Str) : [] -> [Doc] @M;\n"
    <> "  gen line : [] -> [Doc] @M;\n"
    <> "  gen cat : [Doc, Doc] -> [Doc] @M;\n"
    <> "  gen indent(depth:Int) : [Doc] -> [Doc] @M;\n"
    <> "}\n"
    <> "pipeline p where {\n"
    <> "  extract Doc { stdout = true };\n"
    <> "}\n"
    <> "run main using p where {\n"
    <> "  source doctrine RenamedBuiltinParams;\n"
    <> "  source mode M;\n"
    <> "}\n"
    <> "---\n"
    <> "text(\"a\") * (line * text(\"b\"); cat); cat; indent(2)\n"
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
    <> "  gen Str : [] -> [M.U_M] @M;\n"
    <> "  literal Str @M = string;\n"
    <> "  gen Int : [] -> [M.U_M] @M;\n"
    <> "  literal Int @M = int;\n"
    <> "  gen Doc : [] -> [M.U_M] @M;\n"
    <> "  gen empty : [] -> [Doc] @M;\n"
    <> "  gen text(s:Str) : [] -> [Doc] @M;\n"
    <> "  gen line : [] -> [Doc] @M;\n"
    <> "  gen indent(n:Int) : [Doc] -> [Doc] @M;\n"
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


badTextLiteralKindProgram :: Text
badTextLiteralKindProgram =
  "doctrine BadTextLiteralKind where {\n"
    <> "  mode M acyclic classifiedBy M via M.U_M;\n"
    <> "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;\n"
    <> "  gen comp_var(a@M) : [a] -> [a] @M;\n"
    <> "  gen comp_reindex(a@M) : [a] -> [a] @M;\n"
    <> "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };\n"
    <> "  gen U_M : [] -> [M.U_M] @M;\n"
    <> "  gen Bad : [] -> [M.U_M] @M;\n"
    <> "  literal Bad @M = int;\n"
    <> "  gen Int : [] -> [M.U_M] @M;\n"
    <> "  literal Int @M = int;\n"
    <> "  gen Doc : [] -> [M.U_M] @M;\n"
    <> "  gen empty : [] -> [Doc] @M;\n"
    <> "  gen text(s:Bad) : [] -> [Doc] @M;\n"
    <> "  gen line : [] -> [Doc] @M;\n"
    <> "  gen cat : [Doc, Doc] -> [Doc] @M;\n"
    <> "  gen indent(n:Int) : [Doc] -> [Doc] @M;\n"
    <> "}\n"
    <> "pipeline p where {\n"
    <> "  extract Doc { stdout = true };\n"
    <> "}\n"
    <> "run main using p where {\n"
    <> "  source doctrine BadTextLiteralKind;\n"
    <> "  source mode M;\n"
    <> "}\n"
    <> "---\n"
    <> "empty\n"
    <> "---\n"


badTextExtraParamProgram :: Text
badTextExtraParamProgram =
  "doctrine BadTextExtraParam where {\n"
    <> "  mode M acyclic classifiedBy M via M.U_M;\n"
    <> "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;\n"
    <> "  gen comp_var(a@M) : [a] -> [a] @M;\n"
    <> "  gen comp_reindex(a@M) : [a] -> [a] @M;\n"
    <> "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };\n"
    <> "  gen U_M : [] -> [M.U_M] @M;\n"
    <> "  gen Str : [] -> [M.U_M] @M;\n"
    <> "  literal Str @M = string;\n"
    <> "  gen Int : [] -> [M.U_M] @M;\n"
    <> "  literal Int @M = int;\n"
    <> "  gen Doc : [] -> [M.U_M] @M;\n"
    <> "  gen empty : [] -> [Doc] @M;\n"
    <> "  gen text(lhs:Str, rhs:Str) : [] -> [Doc] @M;\n"
    <> "  gen line : [] -> [Doc] @M;\n"
    <> "  gen cat : [Doc, Doc] -> [Doc] @M;\n"
    <> "  gen indent(n:Int) : [Doc] -> [Doc] @M;\n"
    <> "}\n"
    <> "pipeline p where {\n"
    <> "  extract Doc { stdout = true };\n"
    <> "}\n"
    <> "run main using p where {\n"
    <> "  source doctrine BadTextExtraParam;\n"
    <> "  source mode M;\n"
    <> "}\n"
    <> "---\n"
    <> "empty\n"
    <> "---\n"


badIndentLiteralKindProgram :: Text
badIndentLiteralKindProgram =
  "doctrine BadIndentLiteralKind where {\n"
    <> "  mode M acyclic classifiedBy M via M.U_M;\n"
    <> "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;\n"
    <> "  gen comp_var(a@M) : [a] -> [a] @M;\n"
    <> "  gen comp_reindex(a@M) : [a] -> [a] @M;\n"
    <> "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };\n"
    <> "  gen U_M : [] -> [M.U_M] @M;\n"
    <> "  gen Str : [] -> [M.U_M] @M;\n"
    <> "  literal Str @M = string;\n"
    <> "  gen Path : [] -> [M.U_M] @M;\n"
    <> "  literal Path @M = string;\n"
    <> "  gen Doc : [] -> [M.U_M] @M;\n"
    <> "  gen empty : [] -> [Doc] @M;\n"
    <> "  gen text(s:Str) : [] -> [Doc] @M;\n"
    <> "  gen line : [] -> [Doc] @M;\n"
    <> "  gen cat : [Doc, Doc] -> [Doc] @M;\n"
    <> "  gen indent(path:Path) : [Doc] -> [Doc] @M;\n"
    <> "}\n"
    <> "pipeline p where {\n"
    <> "  extract Doc { stdout = true };\n"
    <> "}\n"
    <> "run main using p where {\n"
    <> "  source doctrine BadIndentLiteralKind;\n"
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
    <> "  gen Str : [] -> [M.U_M] @M;\n"
    <> "  literal Str @M = string;\n"
    <> "  gen Int : [] -> [M.U_M] @M;\n"
    <> "  literal Int @M = int;\n"
    <> "  gen Doc : [] -> [M.U_M] @M;\n"
    <> "  gen FileTree : [] -> [M.U_M] @M;\n"
    <> "  gen empty : [] -> [Doc] @M;\n"
    <> "  gen text(s:Str) : [] -> [Doc] @M;\n"
    <> "  gen line : [] -> [Doc] @M;\n"
    <> "  gen cat : [Doc, Doc] -> [Doc] @M;\n"
    <> "  gen indent(n:Int) : [Doc] -> [Doc] @M;\n"
    <> "  gen singleFile(path:Str) : [] -> [FileTree] @M;\n"
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
    <> "singleFile(\"main.mjs\")\n"
    <> "---\n"


badSingleFileExtraParamProgram :: Text
badSingleFileExtraParamProgram =
  "doctrine BadSingleFileExtraParam where {\n"
    <> "  mode M acyclic classifiedBy M via M.U_M;\n"
    <> "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;\n"
    <> "  gen comp_var(a@M) : [a] -> [a] @M;\n"
    <> "  gen comp_reindex(a@M) : [a] -> [a] @M;\n"
    <> "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };\n"
    <> "  gen U_M : [] -> [M.U_M] @M;\n"
    <> "  gen Str : [] -> [M.U_M] @M;\n"
    <> "  literal Str @M = string;\n"
    <> "  gen Int : [] -> [M.U_M] @M;\n"
    <> "  literal Int @M = int;\n"
    <> "  gen Doc : [] -> [M.U_M] @M;\n"
    <> "  gen FileTree : [] -> [M.U_M] @M;\n"
    <> "  gen empty : [] -> [Doc] @M;\n"
    <> "  gen text(s:Str) : [] -> [Doc] @M;\n"
    <> "  gen line : [] -> [Doc] @M;\n"
    <> "  gen cat : [Doc, Doc] -> [Doc] @M;\n"
    <> "  gen indent(n:Int) : [Doc] -> [Doc] @M;\n"
    <> "  gen singleFile(path:Str, suffix:Str) : [Doc] -> [FileTree] @M;\n"
    <> "  gen concatTree : [FileTree, FileTree] -> [FileTree] @M;\n"
    <> "}\n"
    <> "pipeline p where {\n"
    <> "  extract FileTree { root = \"./out\" };\n"
    <> "}\n"
    <> "run main using p where {\n"
    <> "  source doctrine BadSingleFileExtraParam;\n"
    <> "  source mode M;\n"
    <> "}\n"
    <> "---\n"
    <> "empty; singleFile(\"main.mjs\", \"backup\")\n"
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
