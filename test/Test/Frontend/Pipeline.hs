{-# LANGUAGE OverloadedStrings #-}
module Test.Frontend.Pipeline
  ( tests
  ) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import Strat.DSL.Parse (parseRawFile)
import Strat.DSL.Elab (elabRawFileWithEnv)
import Strat.Frontend.Env (ModuleEnv, emptyEnv, meDoctrines)
import Strat.Frontend.Prelude (preludeDoctrines)
import Strat.Frontend.Run (selectRun, runWithEnv, RunResult(..), Artifact(..))
import Strat.Poly.Attr (AttrLit(..), AttrTerm(..))
import Strat.Poly.Graph (BinderArg(..), Diagram(..), Edge(..), EdgePayload(..))
import Strat.Poly.Names (GenName(..))


tests :: TestTree
tests =
  testGroup
    "Frontend.Pipeline"
    [ testCase "derived transform requires acyclic mode" testDerivedRequiresAcyclic
    , testCase "quote without with{} uses derived default policy" testDerivedDefaultPolicy
    , testCase "quoted diagrams can feed ordinary morphisms from the derived doctrine" testApplyDerivedSourceMorphism
    , testCase "let_g preserves generator attrs" testApplyDerivedAttrReflection
    , testCase "let_g preserves binder subprograms" testApplyDerivedBinderReflection
    , testCase "quote internalizes duplicate role" testDuplicateRoleInternalized
    , testCase "quote internalizes alias role" testAliasRoleInternalized
    , testCase "quote memoizes exact repeated shareable subterms" testShareMemoized
    , testCase "quote leaves repeated residual subterms duplicated" testResidualDuplicated
    ]


testDerivedRequiresAcyclic :: Assertion
testDerivedRequiresAcyclic =
  case elabProgram nonAcyclicDerivedProgram of
    Left err ->
      assertBool "expected acyclic-mode rejection" ("acyclic" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected elaboration to reject non-acyclic derived doctrine"


testDerivedDefaultPolicy :: Assertion
testDerivedDefaultPolicy = do
  result <- runNamed defaultPolicyProgram "main"
  diag <- requireDiagram result
  assertBool "expected reserved p0 to be honored via derived default policy" (hasRefNamed "p0_1" diag)


testApplyDerivedSourceMorphism :: Assertion
testApplyDerivedSourceMorphism = do
  result <- runNamed derivedSourceMorphismProgram "main"
  assertBool "expected quoted morphism output to mention generator a" ("a" `T.isInfixOf` prOutput result)
  assertBool "expected quoted morphism output to mention generator b" ("b" `T.isInfixOf` prOutput result)


testApplyDerivedAttrReflection :: Assertion
testApplyDerivedAttrReflection = do
  result <- runNamed derivedAttrReflectionProgram "main"
  assertBool "expected quoted morphism output to contain literal payload" ("hello" `T.isInfixOf` prOutput result)


testApplyDerivedBinderReflection :: Assertion
testApplyDerivedBinderReflection = do
  result <- runNamed derivedBinderReflectionProgram "main"
  assertBool "expected quoted morphism output to include binder step marker" ("wrap" `T.isInfixOf` prOutput result)
  assertBool "expected quoted morphism output to include binder body payload" ("inner" `T.isInfixOf` prOutput result)


testDuplicateRoleInternalized :: Assertion
testDuplicateRoleInternalized = do
  result <- runNamed duplicateInternalizedProgram "main"
  diag <- requireDiagram result
  assertEqual "expected duplicate role to suppress let_dup" 0 (countGenEdges "let_dup" diag)


testAliasRoleInternalized :: Assertion
testAliasRoleInternalized = do
  result <- runNamed aliasInternalizedProgram "main"
  diag <- requireDiagram result
  assertEqual "expected alias role to suppress let_idLike" 0 (countGenEdges "let_idLike" diag)


testShareMemoized :: Assertion
testShareMemoized = do
  result <- runNamed shareMemoizedProgram "main"
  diag <- requireDiagram result
  assertEqual "expected one let_f in quoted diagram" 1 (countGenEdges "let_f" diag)
  assertEqual "expected duplicate role to suppress let_dup" 0 (countGenEdges "let_dup" diag)


testResidualDuplicated :: Assertion
testResidualDuplicated = do
  result <- runNamed residualDuplicatedProgram "main"
  diag <- requireDiagram result
  assertEqual "expected two let_f edges in quoted diagram" 2 (countGenEdges "let_f" diag)


runNamed :: Text -> Text -> IO RunResult
runNamed src runName = do
  env <- require (elabProgram src)
  runDef <- require (selectRun env (Just runName))
  require (runWithEnv env runDef)


requireDiagram :: RunResult -> IO Diagram
requireDiagram result =
  case prArtifact result of
    ArtDiagram _ diag -> pure diag
    ArtExtracted{} -> assertFailure "expected quoted diagram artifact" >> fail "unreachable"


countGenEdges :: Text -> Diagram -> Int
countGenEdges name diag =
  sum (map countEdge (IM.elems (dEdges diag)))
  where
    countEdge edge =
      case ePayload edge of
        PGen (GenName g) _ bargs ->
          (if g == name then 1 else 0) + sum (map countBinderArg bargs)
        PBox _ inner -> countGenEdges name inner
        PFeedback inner -> countGenEdges name inner
        _ -> 0

    countBinderArg barg =
      case barg of
        BAConcrete inner -> countGenEdges name inner
        BAMeta _ -> 0


hasRefNamed :: Text -> Diagram -> Bool
hasRefNamed target diag =
  any isNamed (IM.elems (dEdges diag))
  where
    isNamed edge =
      case ePayload edge of
        PGen (GenName "ref") attrs _ ->
          case M.lookup "name" attrs of
            Just (ATLit (ALString s)) -> s == target
            _ -> False
        _ -> False


nonAcyclicDerivedProgram :: Text
nonAcyclicDerivedProgram =
  T.unlines
    [ "doctrine D where {"
    , "  mode M classifiedBy M via U_M;"
    , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
    , "  gen comp_var(a@M) : [a] -> [a] @M;"
    , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
    , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "  gen U_M : [] -> [U_M] @M;"
    , "  gen T : [] -> [U_M] @M;"
    , "  gen a : [] -> [T] @M;"
    , "}"
    , "fragment Share in D mode M where {"
    , "}"
    , "derived doctrine D_Share = letgraph Share;"
    ]


defaultPolicyProgram :: Text
defaultPolicyProgram =
  T.concat
    [ baseDoctrine
    , "fragment Share in D mode M where {\n}\n"
    , "derived doctrine D_Share = letgraph Share with {\n"
    , "  reserved = [\"p0\"];\n"
    , "};\n"
    , "pipeline p where {\n"
    , "  quote into D_Share;\n"
    , "}\n"
    , runHeader "p"
    , "a\n"
    , runFooter
    ]


derivedSourceMorphismProgram :: Text
derivedSourceMorphismProgram =
  T.concat
    [ doctrineWithOps ["gen a : [] -> [I] @M;", "gen b : [I] -> [I] @M;"]
    , "fragment Share in D mode M where {\n}\n"
    , "derived doctrine D_Share = letgraph Share;\n"
    , "morphism emitShare : D_Share -> Doc where {\n"
    , "  mode M -> Doc;\n"
    , "  attrsort __quote_str -> Str;\n"
    , shareDocPreludeMappings
    , shareDocStructuralMappings
    , "  gen let_a @M -> ((((text(s = \"a\") * id[Doc]) ; cat) * splice(?b0)) ; cat)\n"
    , "  gen let_b @M -> ((((((text(s = \"b\") * id[Doc]) ; cat) * id[Doc]) ; cat) * splice(?b0)) ; cat)\n"
    , "}\n"
    , "pipeline p where {\n"
    , "  quote into D_Share;\n"
    , "  apply emitShare;\n"
    , "  extract Doc { stdout = true; };\n"
    , "}\n"
    , runHeader "p"
    , "a; b\n"
    , runFooter
    ]


derivedAttrReflectionProgram :: Text
derivedAttrReflectionProgram =
  T.concat
    [ doctrineWithOps
        [ "attrsort Str = string;"
        , "gen lit { n:Str } : [] -> [I] @M;"
        ]
    , "fragment Share in D mode M where {\n}\n"
    , "derived doctrine D_Share = letgraph Share;\n"
    , "morphism emitShare : D_Share -> Doc where {\n"
    , "  mode M -> Doc;\n"
    , "  attrsort __quote_str -> Str;\n"
    , "  attrsort Str -> Str;\n"
    , shareDocPreludeMappings
    , shareDocStructuralMappings
    , "  gen let_lit @M -> ((((text(s = n) * id[Doc]) ; cat) * splice(?b0)) ; cat)\n"
    , "}\n"
    , "pipeline p where {\n"
    , "  quote into D_Share;\n"
    , "  apply emitShare;\n"
    , "  extract Doc { stdout = true; };\n"
    , "}\n"
    , runHeader "p"
    , "lit(n = \"hello\")\n"
    , runFooter
    ]


derivedBinderReflectionProgram :: Text
derivedBinderReflectionProgram =
  T.concat
    [ doctrineWithOps
        [ "attrsort Str = string;"
        , "gen lit { n:Str } : [] -> [I] @M;"
        , "gen wrap : [binder { } : [I]] -> [I] @M;"
        ]
    , "fragment Share in D mode M where {\n"
    , "  recurse binders = true;\n"
    , "}\n"
    , "derived doctrine D_Share = letgraph Share;\n"
    , "morphism emitShare : D_Share -> Doc where {\n"
    , "  mode M -> Doc;\n"
    , "  attrsort __quote_str -> Str;\n"
    , "  attrsort Str -> Str;\n"
    , shareDocPreludeMappings
    , shareDocStructuralMappings
    , "  gen let_lit @M -> ((((text(s = n) * id[Doc]) ; cat) * splice(?b0)) ; cat)\n"
    , "  gen let_wrap @M -> ((((((text(s = \"wrap \") * id[Doc]) ; cat) * id[Doc]) ; cat) * splice(?b0)) ; cat)\n"
    , "}\n"
    , "pipeline p where {\n"
    , "  quote into D_Share;\n"
    , "  apply emitShare;\n"
    , "  extract Doc { stdout = true; };\n"
    , "}\n"
    , runHeader "p"
    , "wrap [lit(n = \"inner\")]\n"
    , runFooter
    ]


duplicateInternalizedProgram :: Text
duplicateInternalizedProgram =
  T.concat
    [ doctrineWithOps
        [ "gen a : [] -> [I] @M;"
        ]
    , "fragment Share in D mode M where {\n"
    , "  gen dup = duplicate;\n"
    , "}\n"
    , "derived doctrine D_Share = letgraph Share;\n"
    , "pipeline p where {\n"
    , "  quote into D_Share;\n"
    , "}\n"
    , runHeader "p"
    , "a ; dup{I}\n"
    , runFooter
    ]


aliasInternalizedProgram :: Text
aliasInternalizedProgram =
  T.concat
    [ doctrineWithOps
        [ "gen a : [] -> [I] @M;"
        ]
    , "fragment Share in D mode M where {\n"
    , "  gen idLike = alias;\n"
    , "}\n"
    , "derived doctrine D_Share = letgraph Share;\n"
    , "pipeline p where {\n"
    , "  quote into D_Share;\n"
    , "}\n"
    , runHeader "p"
    , "a ; idLike\n"
    , runFooter
    ]


shareMemoizedProgram :: Text
shareMemoizedProgram =
  T.concat
    [ doctrineWithOps
        [ "gen a : [] -> [I] @M;"
        ]
    , "fragment Share in D mode M where {\n"
    , "  gen dup = duplicate;\n"
    , "  gen f = share;\n"
    , "}\n"
    , "derived doctrine D_Share = letgraph Share;\n"
    , "pipeline p where {\n"
    , "  quote into D_Share;\n"
    , "}\n"
    , runHeader "p"
    , "a ; dup{I} ; (f * f)\n"
    , runFooter
    ]


residualDuplicatedProgram :: Text
residualDuplicatedProgram =
  T.concat
    [ doctrineWithOps
        [ "gen a : [] -> [I] @M;"
        ]
    , "fragment Share in D mode M where {\n"
    , "  gen dup = duplicate;\n"
    , "}\n"
    , "derived doctrine D_Share = letgraph Share;\n"
    , "pipeline p where {\n"
    , "  quote into D_Share;\n"
    , "}\n"
    , runHeader "p"
    , "a ; dup{I} ; (f * f)\n"
    , runFooter
    ]


baseDoctrine :: Text
baseDoctrine =
  doctrineWithOps ["gen a : [I] -> [I] @M;"]


doctrineWithOps :: [Text] -> Text
doctrineWithOps ops =
  T.unlines
    ( [ "doctrine D where {"
      , "  mode M acyclic classifiedBy M via U_M;"
      , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
      , "  gen comp_var(a@M) : [a] -> [a] @M;"
      , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
      , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
      , "  gen U_M : [] -> [U_M] @M;"
      , "  gen I : [] -> [U_M] @M;"
      , "  gen dup(a@M) : [a] -> [a, a] @M;"
      , "  gen idLike : [I] -> [I] @M;"
      , "  gen f : [I] -> [I] @M;"
      ]
        <> map ("  " <>) ops
        <> ["}"]
    )


shareDocPreludeMappings :: Text
shareDocPreludeMappings =
  T.unlines
    [ "  type Ref @M -> Doc @Doc;"
    , "  type RefList @M -> Doc @Doc;"
    , "  type LetGraph @M -> Doc @Doc;"
    , "  gen ref @M -> text(s = name)"
    , "  gen refsNil @M -> empty"
    , "  gen refsCons @M -> cat"
    , "  gen returnRefs @M -> id[Doc]"
    , "  gen letGraphProgram @M -> (id[Doc] * id[Doc]) ; cat"
    ]


shareDocStructuralMappings :: Text
shareDocStructuralMappings =
  T.unlines
    [ "  gen let_U_M @M -> (id[Doc] * splice(?b0)) ; cat"
    , "  gen let_I @M -> (id[Doc] * splice(?b0)) ; cat"
    , "  gen let_comp_ctx_ext @M -> ((((id[Doc] * id[Doc]) ; cat) * splice(?b0)) ; cat)"
    , "  gen let_comp_var @M -> ((((id[Doc] * id[Doc]) ; cat) * splice(?b0)) ; cat)"
    , "  gen let_comp_reindex @M -> ((((id[Doc] * id[Doc]) ; cat) * splice(?b0)) ; cat)"
    , "  gen let_dup @M -> ((((((id[Doc] * id[Doc]) ; cat) * id[Doc]) ; cat) * splice(?b0)) ; cat)"
    , "  gen let_idLike @M -> ((((id[Doc] * id[Doc]) ; cat) * splice(?b0)) ; cat)"
    , "  gen let_f @M -> ((((id[Doc] * id[Doc]) ; cat) * splice(?b0)) ; cat)"
    , "  gen letBox @M -> ((((((id[Doc] * id[Doc]) ; cat) * id[Doc]) ; cat) * splice(?b0)) ; cat)"
    , "  gen letFeedback @M -> ((((((id[Doc] * id[Doc]) ; cat) * id[Doc]) ; cat) * splice(?b0)) ; cat)"
    ]


runHeader :: Text -> Text
runHeader pipelineName =
  T.unlines
    [ "run main using " <> pipelineName <> " where {"
    , "  source doctrine D;"
    , "  source mode M;"
    , "}"
    , "---"
    ]


runFooter :: Text
runFooter =
  T.unlines
    [ "---"
    ]


elabProgram :: Text -> Either Text ModuleEnv
elabProgram src = do
  raw <- parseRawFile src
  let baseEnv = emptyEnv { meDoctrines = preludeDoctrines }
  elabRawFileWithEnv baseEnv raw


require :: Either Text a -> IO a
require (Left err) = assertFailure (show err) >> fail "unreachable"
require (Right a) = pure a
