{-# LANGUAGE OverloadedStrings #-}
module Test.Frontend.Pipeline
  ( tests
  ) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import Strat.DSL.Parse (parseRawFile)
import Strat.DSL.Elab (elabRawFileWithEnv)
import Strat.Frontend.Env (ModuleEnv, emptyEnv, meDoctrines, meMorphisms)
import Strat.Frontend.Prelude (preludeDoctrines)
import Strat.Frontend.Run (selectRun, runWithEnv, RunResult(..), Artifact(..))
import Strat.Poly.Foliation (SSA(..))


tests :: TestTree
tests =
  testGroup
    "Frontend.Pipeline"
    [ testCase "pipeline foliate + forget roundtrip smoke" testPipelineRoundtrip
    , testCase "derived doctrine requires acyclic mode" testDerivedRequiresAcyclic
    , testCase "extract foliate without with{} uses derived default policy" testDerivedDefaultPolicy
    , testCase "derived doctrine reserves and materializes .forget" testDerivedForgetReservedAndMaterialized
    , testCase "ArtSSA can apply morphism sourced from derived doctrine" testApplyDerivedSourceMorphism
    ]


testPipelineRoundtrip :: Assertion
testPipelineRoundtrip = do
  env <- require (elabProgram program)
  runDef <- require (selectRun env (Just "main"))
  result <- require (runWithEnv env runDef)
  assertBool "expected diagram output" ("edges:" `T.isInfixOf` prOutput result)


testDerivedRequiresAcyclic :: Assertion
testDerivedRequiresAcyclic =
  case elabProgram nonAcyclicDerivedProgram of
    Left err ->
      assertBool "expected acyclic-mode rejection" ("acyclic" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected elaboration to reject non-acyclic derived doctrine"


testDerivedDefaultPolicy :: Assertion
testDerivedDefaultPolicy = do
  env <- require (elabProgram defaultPolicyProgram)
  runDef <- require (selectRun env (Just "main"))
  result <- require (runWithEnv env runDef)
  case prArtifact result of
    ArtSSA _ _ ssa ->
      assertBool "expected reserved p0 to be honored via derived default policy" ("p0_1" `elem` M.elems (ssaPortNames ssa))
    _ ->
      assertFailure "expected ArtSSA result"


testDerivedForgetReservedAndMaterialized :: Assertion
testDerivedForgetReservedAndMaterialized = do
  env <- require (elabProgram derivedMaterializedProgram)
  assertBool "expected synthesized D_SSA.forget morphism" (M.member "D_SSA.forget" (meMorphisms env))
  case elabProgram forgetCollisionProgram of
    Left _ ->
      pure ()
    Right _ ->
      assertFailure "expected derived doctrine insertion to reject preexisting D_SSA.forget"


testApplyDerivedSourceMorphism :: Assertion
testApplyDerivedSourceMorphism = do
  env <- require (elabProgram derivedSourceMorphismProgram)
  runDef <- require (selectRun env (Just "main"))
  result <- require (runWithEnv env runDef)
  assertBool "expected SSA morphism output to mention generator a" ("a" `T.isInfixOf` prOutput result)
  assertBool "expected SSA morphism output to mention generator b" ("b" `T.isInfixOf` prOutput result)


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


nonAcyclicDerivedProgram :: Text
nonAcyclicDerivedProgram =
  "doctrine D where {\n"
    <> "  mode M;\n"
    <> "  type T @M;\n"
    <> "  gen a : [] -> [T] @M;\n"
    <> "}\n"
    <> "derived doctrine D_SSA = foliated D mode M;\n"


defaultPolicyProgram :: Text
defaultPolicyProgram =
  "doctrine D where {\n"
    <> "  mode M acyclic;\n"
    <> "  type T @M;\n"
    <> "  gen a : [T] -> [T] @M;\n"
    <> "}\n"
    <> "derived doctrine D_SSA = foliated D mode M with {\n"
    <> "  reserved = [\"p0\"];\n"
    <> "};\n"
    <> "pipeline p where {\n"
    <> "  extract foliate into D_SSA;\n"
    <> "}\n"
    <> "run main using p where {\n"
    <> "  source doctrine D;\n"
    <> "  source mode M;\n"
    <> "}\n"
    <> "---\n"
    <> "a\n"
    <> "---\n"


derivedMaterializedProgram :: Text
derivedMaterializedProgram =
  "doctrine D where {\n"
    <> "  mode M acyclic;\n"
    <> "  type T @M;\n"
    <> "  gen a : [] -> [T] @M;\n"
    <> "}\n"
    <> "derived doctrine D_SSA = foliated D mode M;\n"


forgetCollisionProgram :: Text
forgetCollisionProgram =
  "doctrine D where {\n"
    <> "  mode M acyclic;\n"
    <> "  type T @M;\n"
    <> "  gen a : [] -> [T] @M;\n"
    <> "}\n"
    <> "morphism D_SSA.forget : D -> D where {\n"
    <> "  mode M -> M;\n"
    <> "  type T @M -> T @M;\n"
    <> "  gen a @M -> a;\n"
    <> "}\n"
    <> "derived doctrine D_SSA = foliated D mode M;\n"


derivedSourceMorphismProgram :: Text
derivedSourceMorphismProgram =
  "doctrine D where {\n"
    <> "  mode M acyclic;\n"
    <> "  type T @M;\n"
    <> "  gen a : [] -> [T] @M;\n"
    <> "  gen b : [T] -> [] @M;\n"
    <> "}\n"
    <> "derived doctrine D_SSA = foliated D mode M;\n"
    <> "morphism emitSSA : D_SSA -> Doc where {\n"
    <> "  mode M -> Doc;\n"
    <> "  attrsort Str -> Str;\n"
    <> "  type PortRef @M -> Doc @Doc;\n"
    <> "  type PortList @M -> Doc @Doc;\n"
    <> "  type Step @M -> Doc @Doc;\n"
    <> "  type StepList @M -> Doc @Doc;\n"
    <> "  type SSA @M -> Doc @Doc;\n"
    <> "  gen portRef @M -> text(s = name)\n"
    <> "  gen portsNil @M -> empty\n"
    <> "  gen portsCons @M -> cat\n"
    <> "  gen stepGen @M -> ((text(s = name) * id[Doc]) ; cat) * id[Doc] ; cat\n"
    <> "  gen stepBox @M -> ((text(s = name) * id[Doc]) ; cat) * id[Doc] ; cat\n"
    <> "  gen stepFeedback @M -> ((text(s = \"feedback\") * id[Doc]) ; cat) * id[Doc] ; cat\n"
    <> "  gen stepsNil @M -> empty\n"
    <> "  gen stepsCons @M -> cat\n"
    <> "  gen ssaProgram @M -> ((id[Doc] * id[Doc]) ; cat) * id[Doc] ; cat\n"
    <> "}\n"
    <> "pipeline p where {\n"
    <> "  extract foliate into D_SSA;\n"
    <> "  apply emitSSA;\n"
    <> "  extract Doc { stdout = true; };\n"
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
