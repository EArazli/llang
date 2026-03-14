{-# LANGUAGE OverloadedStrings #-}
module Test.Value.Doc
  ( tests
  ) where

import qualified Data.Map.Strict as M
import Data.Text (Text)
import qualified Data.Text as T
import Strat.DSL.Elab (elabRawFileWithEnv)
import Strat.DSL.Parse (parseRawFile)
import Strat.Frontend.Build (BuildProduct(..), BuildResult(..), buildWithEnv, selectBuild)
import Strat.Frontend.Env (ModuleEnv, emptyEnv, meDoctrines)
import Strat.Frontend.Prelude (preludeDoctrines)
import Strat.Host.Backend (HostArtifact(..))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit

tests :: TestTree
tests =
  testGroup
    "Value.Doc"
    [ testCase "Doc emitter renders indent/cat/line" testDocExtraction
    , testCase "FileTree emitter renders embedded Doc content" testArtifactFileTreeExtraction
    , testCase "Doc emitter works for doctrines extending Doc" testExtendedDocExtraction
    , testCase "FileTree emitter works for doctrines extending Artifact" testExtendedArtifactFileTreeExtraction
    , testCase "Doc emitter ignores builtin parameter names" testDocExtractionIgnoresBuiltinParamNames
    , testCase "Doc emitter rejects doctrines missing required generators" testDocExtractionMissingGenerator
    , testCase "Doc emitter rejects non-string text literal type" testDocExtractionWrongLiteralKind
    , testCase "Doc emitter rejects text with extra term parameters" testDocExtractionExtraTextParam
    , testCase "Doc emitter rejects indent with non-int literal type" testDocExtractionWrongIndentLiteralKind
    , testCase "FileTree emitter rejects wrong singleFile signature" testFileTreeExtractionWrongSingleFileSig
    , testCase "FileTree emitter rejects singleFile with extra term parameters" testFileTreeExtractionExtraSingleFileParam
    ]

testDocExtraction :: Assertion
testDocExtraction = do
  result <- require (runProgram docProgram)
  brOutput result @?= "a\n  b"

testArtifactFileTreeExtraction :: Assertion
testArtifactFileTreeExtraction = do
  result <- require (runProgram artifactFileTreeProgram)
  case brArtifact result of
    BPHost HostArtifact { haFiles = files } ->
      M.lookup "./out/hello.txt" files @?= Just "hello"
    _ ->
      assertFailure "expected emitted FileTree artifact"

testExtendedDocExtraction :: Assertion
testExtendedDocExtraction = do
  result <- require (runProgram extendedDocProgram)
  brOutput result @?= "(x)"

testExtendedArtifactFileTreeExtraction :: Assertion
testExtendedArtifactFileTreeExtraction = do
  result <- require (runProgram extendedArtifactFileTreeProgram)
  case brArtifact result of
    BPHost HostArtifact { haFiles = files } ->
      M.lookup "./out/main.mjs" files @?= Just "console.log('hello');"
    _ ->
      assertFailure "expected emitted FileTree artifact"

testDocExtractionIgnoresBuiltinParamNames :: Assertion
testDocExtractionIgnoresBuiltinParamNames = do
  result <- require (runProgram renamedBuiltinParamProgram)
  brOutput result @?= "a\n  b"

testDocExtractionMissingGenerator :: Assertion
testDocExtractionMissingGenerator = do
  err <- requireLeft (runProgram missingCatProgram)
  assertBool "expected missing cat diagnostic" ("missing generator 'cat' in mode M" `T.isInfixOf` err)

testDocExtractionWrongLiteralKind :: Assertion
testDocExtractionWrongLiteralKind = do
  err <- requireLeft (runProgram badTextLiteralKindProgram)
  assertBool "expected text parameter literal kind diagnostic" ("generator 'text' sole term parameter must admit string literals" `T.isInfixOf` err)

testDocExtractionExtraTextParam :: Assertion
testDocExtractionExtraTextParam = do
  err <- requireLeft (runProgram badTextExtraParamProgram)
  assertBool "expected text arity diagnostic" ("generator 'text' must have exactly one sole term parameter" `T.isInfixOf` err)

testDocExtractionWrongIndentLiteralKind :: Assertion
testDocExtractionWrongIndentLiteralKind = do
  err <- requireLeft (runProgram badIndentLiteralKindProgram)
  assertBool "expected indent parameter literal kind diagnostic" ("generator 'indent' sole term parameter must admit int literals" `T.isInfixOf` err)

testFileTreeExtractionWrongSingleFileSig :: Assertion
testFileTreeExtractionWrongSingleFileSig = do
  err <- requireLeft (runProgram badSingleFileSigProgram)
  assertBool "expected singleFile signature diagnostic" ("generator 'singleFile' has wrong signature; expected [Doc]->[FileTree] in mode M" `T.isInfixOf` err)

testFileTreeExtractionExtraSingleFileParam :: Assertion
testFileTreeExtractionExtraSingleFileParam = do
  err <- requireLeft (runProgram badSingleFileExtraParamProgram)
  assertBool "expected singleFile arity diagnostic" ("generator 'singleFile' must have exactly one sole term parameter" `T.isInfixOf` err)

docProgram :: Text
docProgram =
  docBuildProgram "DocLang" "Doc" "Doc" "text(\"a\") * (line * text(\"b\"); cat); cat; indent(2)" $
    T.unlines
      [ "pipeline p where {"
      , "  project export main;"
      , "  emit via Doc { stdout = true; };"
      , "}"
      ]

artifactFileTreeProgram :: Text
artifactFileTreeProgram =
  docBuildProgram "ArtifactLang" "Artifact" "Artifact" "text(\"hello\"); singleFile(\"hello.txt\")" $
    T.unlines
      [ "pipeline p where {"
      , "  project export main;"
      , "  emit via FileTree { root = \"./out\" };"
      , "}"
      ]

extendedDocProgram :: Text
extendedDocProgram =
  "doctrine PrettyDoc extends Doc where {\n"
    <> "  gen parens : [Doc] -> [Doc] @Doc;\n"
    <> "  rule computational parens_def -> : [Doc] -> [Doc] @Doc =\n"
    <> "    parens == (text(\"(\") * id[Doc]) ; cat ; (id[Doc] * text(\")\")) ; cat\n"
    <> "}\n"
    <> docBuildProgram "PrettyDocLang" "PrettyDoc" "Doc" "text(\"x\"); parens"
         (T.unlines
           [ "pipeline p where {"
           , "  project export main;"
           , "  normalize { policy = \"computational_lr\"; fuel = 50; };"
           , "  emit via Doc { stdout = true; };"
           , "}"
           ])

extendedArtifactFileTreeProgram :: Text
extendedArtifactFileTreeProgram =
  "doctrine JSArtifact extends Artifact where {\n"
    <> "  gen jsHello : [] -> [Doc] @Artifact;\n"
    <> "  rule computational jsHello_def -> : [] -> [Doc] @Artifact =\n"
    <> "    jsHello == text(\"console.log('hello');\")\n"
    <> "}\n"
    <> docBuildProgram "JSArtifactLang" "JSArtifact" "Artifact" "jsHello; singleFile(\"main.mjs\")"
         (T.unlines
           [ "pipeline p where {"
           , "  project export main;"
           , "  normalize { policy = \"computational_lr\"; fuel = 50; };"
           , "  emit via FileTree { root = \"./out\" };"
           , "}"
           ])

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
    <> docBuildProgram "RenamedBuiltinLang" "RenamedBuiltinParams" "M" "text(\"a\") * (line * text(\"b\"); cat); cat; indent(2)"
         (T.unlines
           [ "pipeline p where {"
           , "  project export main;"
           , "  emit via Doc { stdout = true; };"
           , "}"
           ])

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
    <> docBuildProgram "MissingCatLang" "MissingCat" "M" "empty"
         (T.unlines
           [ "pipeline p where {"
           , "  project export main;"
           , "  emit via Doc { stdout = true; };"
           , "}"
           ])

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
    <> docBuildProgram "BadTextLiteralKindLang" "BadTextLiteralKind" "M" "empty"
         (T.unlines
           [ "pipeline p where {"
           , "  project export main;"
           , "  emit via Doc { stdout = true; };"
           , "}"
           ])

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
    <> docBuildProgram "BadTextExtraParamLang" "BadTextExtraParam" "M" "empty"
         (T.unlines
           [ "pipeline p where {"
           , "  project export main;"
           , "  emit via Doc { stdout = true; };"
           , "}"
           ])

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
    <> docBuildProgram "BadIndentLiteralKindLang" "BadIndentLiteralKind" "M" "empty"
         (T.unlines
           [ "pipeline p where {"
           , "  project export main;"
           , "  emit via Doc { stdout = true; };"
           , "}"
           ])

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
    <> docBuildProgram "BadSingleFileSigLang" "BadSingleFileSig" "M" "singleFile(\"main.mjs\")"
         (T.unlines
           [ "pipeline p where {"
           , "  project export main;"
           , "  emit via FileTree { root = \"./out\" };"
           , "}"
           ])

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
    <> docBuildProgram "BadSingleFileExtraParamLang" "BadSingleFileExtraParam" "M" "empty; singleFile(\"main.mjs\", \"backup\")"
         (T.unlines
           [ "pipeline p where {"
           , "  project export main;"
           , "  emit via FileTree { root = \"./out\" };"
           , "}"
           ])

docBuildProgram :: Text -> Text -> Text -> Text -> Text -> Text
docBuildProgram langName doctrineName modeName exprText pipelineText =
  T.unlines
    [ "module_surface " <> langName <> "Unit where {"
    , "  doctrine " <> doctrineName <> ";"
    , "  mode " <> modeName <> ";"
    , "}"
    , "language " <> langName <> " where {"
    , "  doctrine " <> doctrineName <> ";"
    , "  module_surface " <> langName <> "Unit;"
    , "}"
    , "module Main in " <> langName <> " where {"
    , "  let main"
    , "  ---"
    , exprText
    , "  ---"
    , "  export { main };"
    , "}"
    , T.stripEnd pipelineText
    , "build main from Main using p;"
    ]

runProgram :: Text -> Either Text BuildResult
runProgram src = do
  env <- elabDocProgram src
  buildDef <- selectBuild env (Just "main")
  buildWithEnv env buildDef

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
