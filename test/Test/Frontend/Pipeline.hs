{-# LANGUAGE OverloadedStrings #-}
module Test.Frontend.Pipeline
  ( tests
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Strat.DSL.Elab (elabRawFileWithEnv)
import Strat.DSL.Parse (parseRawFile)
import Strat.Frontend.Build (BuildResult(..), buildWithEnv, selectBuild)
import Strat.Frontend.Env (ModuleEnv, emptyEnv, meDoctrines)
import Strat.Frontend.Prelude (preludeDoctrines)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit

tests :: TestTree
tests =
  testGroup
    "Frontend.Pipeline"
    [ testCase "derived reflected quotation requires acyclic mode" testDerivedRequiresAcyclic
    , testCase "invalid pipeline product flow is rejected during elaboration" testInvalidPipelineFlowRejected
    , testCase "old fragment role syntax is rejected" testOldFragmentSyntaxRejected
    , testCase "old transform-derived syntax is rejected" testOldTransformDerivedSyntaxRejected
    , testCase "old quote policy syntax is rejected" testOldQuotePolicyRejected
    , testCase "emit via JS is rejected as an unsupported host backend" testEmitJsRejected
    , testCase "included generators are shared in reflected output" testIncludedQuoted
    , testCase "excluded generators stay duplicated in reflected output" testResidualQuoted
    , testCase "cross binders false leaves nested sharing disabled" testCrossBindersFalse
    , testCase "cross binders true recursively shares nested bindings" testCrossBindersTrue
    , testCase "pipeline normalize post-pass uses kernel defeq for term diagrams" testPipelineNormalizeUsesDefEq
    ]

testDerivedRequiresAcyclic :: Assertion
testDerivedRequiresAcyclic =
  case elabProgram nonAcyclicProgram of
    Left err ->
      assertBool "expected acyclic-mode rejection" ("acyclic" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected elaboration to reject non-acyclic derived doctrine"

testInvalidPipelineFlowRejected :: Assertion
testInvalidPipelineFlowRejected =
  case elabProgram src of
    Left err ->
      assertBool "expected module-only phase rejection" ("normalize expects" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected elaboration to reject invalid pipeline product flow"
  where
    src =
      T.unlines
        [ "pipeline p where {"
        , "  emit via Doc { stdout = true; };"
        , "  normalize;"
        , "}"
        ]

testOldFragmentSyntaxRejected :: Assertion
testOldFragmentSyntaxRejected =
  assertParseFails $
    T.unlines
      [ baseDoctrine
      , "fragment Share in D mode M where {"
      , "  gen f = share;"
      , "}"
      ]

testOldTransformDerivedSyntaxRejected :: Assertion
testOldTransformDerivedSyntaxRejected =
  assertParseFails $
    T.unlines
      [ baseDoctrine
      , "fragment Share in D mode M where {"
      , "  include gen f;"
      , "}"
      , "derived doctrine D_Q = transform explicit_sharing using Share;"
      ]

testOldQuotePolicyRejected :: Assertion
testOldQuotePolicyRejected =
  assertParseFails $
    T.unlines
      [ baseDoctrine
      , "fragment Share in D mode M where {"
      , "  include gen f;"
      , "}"
      , "derived doctrine D_Q = reflect quotation of D mode M;"
      , "pipeline p where {"
      , "  quote into D_Q with { naming = \"boundary_labels_first\"; };"
      , "}"
      ]

testEmitJsRejected :: Assertion
testEmitJsRejected = do
  env <- require (elabProgram src)
  buildDef <- require (selectBuild env (Just "main"))
  err <- requireLeft (buildWithEnv env buildDef)
  assertBool "expected unknown backend rejection" ("unknown backend" `T.isInfixOf` T.toLower err)
  where
    src =
      T.unlines
        [ baseDoctrine
        , "module_surface QuoteUnit where {"
        , "  doctrine D;"
        , "  mode M;"
        , "}"
        , "language QuoteLang where {"
        , "  doctrine D;"
        , "  module_surface QuoteUnit;"
        , "}"
        , "fragment Share in D mode M where {"
        , "  include gen a;"
        , "}"
        , "derived doctrine D_Q = reflect quotation of D mode M;"
        , "module Main in QuoteLang where {"
        , "  let main"
        , "  ---"
        , "  a"
        , "  ---"
        , "  export { main };"
        , "}"
        , "pipeline p where {"
        , "  project export main;"
        , "  quote using Share into D_Q;"
        , "  emit via JS { stdout = true; };"
        , "}"
        , "build main from Main using p;"
        ]

testIncludedQuoted :: Assertion
testIncludedQuoted = do
  result <- runNamed includedQuoteProgram "main"
  let out = brOutput result
  assertEqual "expected one shared q_a binding" 1 (countOccurrences "q_a" out)
  assertEqual "expected one shared q_f binding" 1 (countOccurrences "q_f" out)
  assertBool "expected reflected q_begin" ("q_begin" `T.isInfixOf` out)
  assertBool "expected reflected RefIds encoding" ("refIds_cons" `T.isInfixOf` out)
  assertBool "expected reflected q_end" ("q_end" `T.isInfixOf` out)

testResidualQuoted :: Assertion
testResidualQuoted = do
  result <- runNamed residualQuoteProgram "main"
  let out = brOutput result
  assertEqual "expected one shared q_a binding" 1 (countOccurrences "q_a" out)
  assertEqual "expected duplicated q_f bindings" 2 (countOccurrences "q_f" out)

testCrossBindersFalse :: Assertion
testCrossBindersFalse = do
  result <- runNamed binderResidualProgram "main"
  let out = brOutput result
  assertEqual "expected nested q_a duplication" 2 (countOccurrences "q_a" out)
  assertEqual "expected nested q_f duplication" 2 (countOccurrences "q_f" out)
  assertBool "expected reflected wrap binding" ("q_wrap" `T.isInfixOf` out)

testCrossBindersTrue :: Assertion
testCrossBindersTrue = do
  result <- runNamed binderIncludedProgram "main"
  let out = brOutput result
  assertEqual "expected nested q_a sharing" 1 (countOccurrences "q_a" out)
  assertEqual "expected nested q_f sharing" 1 (countOccurrences "q_f" out)
  assertBool "expected reflected wrap binding" ("q_wrap" `T.isInfixOf` out)

testPipelineNormalizeUsesDefEq :: Assertion
testPipelineNormalizeUsesDefEq = do
  result <- runNamed transportNormalizeProgram "main"
  let out = brOutput result
  assertBool "expected normalized pipeline output to retain mk22" ("mk22" `T.isInfixOf` out)
  assertBool "expected normalized pipeline output to erase expect22 via defeq post-pass" (not ("expect22" `T.isInfixOf` out))

runNamed :: Text -> Text -> IO BuildResult
runNamed src buildName = do
  env <- require (elabProgram src)
  buildDef <- require (selectBuild env (Just buildName))
  require (buildWithEnv env buildDef)

requireLeft :: Either Text a -> IO Text
requireLeft res =
  case res of
    Left err -> pure err
    Right _ -> assertFailure "expected failure" >> fail "unreachable"

assertParseFails :: Text -> Assertion
assertParseFails src =
  case parseRawFile src of
    Left _ -> pure ()
    Right _ -> assertFailure "expected parse failure"

countOccurrences :: Text -> Text -> Int
countOccurrences needle haystack
  | T.null needle = 0
  | otherwise = go haystack 0
  where
    go txt acc =
      case T.breakOn needle txt of
        (_, rest)
          | T.null rest -> acc
          | otherwise -> go (T.drop (T.length needle) rest) (acc + 1)

elabProgram :: Text -> Either Text ModuleEnv
elabProgram src = do
  raw <- parseRawFile src
  elabRawFileWithEnv env0 raw
  where
    env0 = emptyEnv { meDoctrines = preludeDoctrines }

nonAcyclicProgram :: Text
nonAcyclicProgram =
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
    , "derived doctrine D_Q = reflect quotation of D mode M;"
    ]

includedQuoteProgram :: Text
includedQuoteProgram =
  mkQuoteProgram
    [ "include gen a;"
    , "include gen f;"
    ]
    "((a ; f) * (a ; f)) ; join"

residualQuoteProgram :: Text
residualQuoteProgram =
  mkQuoteProgram
    [ "include gen a;"
    ]
    "((a ; f) * (a ; f)) ; join"

binderResidualProgram :: Text
binderResidualProgram =
  mkQuoteProgram
    [ "include gen a;"
    , "include gen f;"
    , "cross binders = false;"
    ]
    "wrap[((a ; f) * (a ; f)) ; join]"

binderIncludedProgram :: Text
binderIncludedProgram =
  mkQuoteProgram
    [ "include gen a;"
    , "include gen f;"
    , "cross binders = true;"
    ]
    "wrap[((a ; f) * (a ; f)) ; join]"

transportNormalizeProgram :: Text
transportNormalizeProgram =
  T.unlines
    [ "doctrine TransportBuiltin where {"
    , "  mode M classifiedBy M via M.U_M;"
    , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
    , "  gen comp_var(a@M) : [a] -> [a] @M;"
    , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
    , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "  gen U_M : [] -> [M.U_M] @M;"
    , "  mode I classifiedBy I via I.U_I;"
    , "  gen i_ctx_ext(a@I) : [a] -> [a] @I;"
    , "  gen i_var(a@I) : [a] -> [a] @I;"
    , "  gen i_reindex(a@I) : [a] -> [a] @I;"
    , "  comprehension I where { ctx_ext = i_ctx_ext; var = i_var; reindex = i_reindex; };"
    , "  gen U_I : [] -> [I.U_I] @I;"
    , "  gen Nat : [] -> [I.U_I] @I;"
    , "  gen A : [] -> [M.U_M] @M;"
    , "  gen Vec(n : Nat, a@M) : [] -> [M.U_M] @M;"
    , "  gen Z : [] -> [Nat] @I;"
    , "  gen S : [Nat] -> [Nat] @I;"
    , "  gen add : [Nat, Nat] -> [Nat] @I;"
    , "  rule computational addZ -> : [Nat] -> [Nat] @I ="
    , "    (Z * id[Nat]) ; add == id[Nat]"
    , "  rule computational addS -> : [Nat, Nat] -> [Nat] @I ="
    , "    (S * id[Nat]) ; add == add ; S"
    , "  gen mk22(a@M) : [] -> [Vec(S(S(Z)), a)] @M;"
    , "  gen expect22(a@M) : [Vec(add(S(Z), S(Z)), a)] -> [Vec(S(S(Z)), a)] @M;"
    , "}"
    , "module_surface VecRunUnit where {"
    , "  doctrine TransportBuiltin;"
    , "  mode M;"
    , "}"
    , "language VecRunLang where {"
    , "  doctrine TransportBuiltin;"
    , "  module_surface VecRunUnit;"
    , "}"
    , "module VecRuns in VecRunLang where {"
    , "  let main"
    , "  ---"
    , "  mk22(A) ; expect22(A)"
    , "  ---"
    , "  export { main };"
    , "}"
    , "pipeline p where {"
    , "  project export main;"
    , "  normalize { policy = \"topmost\"; fuel = 50; };"
    , "}"
    , "build main from VecRuns using p;"
    ]

mkQuoteProgram :: [Text] -> Text -> Text
mkQuoteProgram fragmentItems exprText =
  T.unlines $
    [ baseDoctrine
    , "module_surface QuoteUnit where {"
    , "  doctrine D;"
    , "  mode M;"
    , "}"
    , "language QuoteLang where {"
    , "  doctrine D;"
    , "  module_surface QuoteUnit;"
    , "}"
    , "fragment Share in D mode M where {"
    ]
      <> map ("  " <>) fragmentItems
      <> [ "}"
         , "derived doctrine D_Q = reflect quotation of D mode M;"
         , "module Main in QuoteLang where {"
         , "  let main"
         , "  ---"
         , exprText
         , "  ---"
         , "  export { main };"
         , "}"
         , "pipeline p where {"
         , "  project export main;"
         , "  quote using Share into D_Q;"
         , "}"
         , "build main from Main using p;"
         ]

baseDoctrine :: Text
baseDoctrine =
  T.unlines
    [ "doctrine D where {"
    , "  mode M acyclic classifiedBy M via M.U_M;"
    , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
    , "  gen comp_var(a@M) : [a] -> [a] @M;"
    , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
    , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "  gen U_M : [] -> [M.U_M] @M;"
    , "  gen T : [] -> [M.U_M] @M;"
    , "  gen a : [] -> [T] @M;"
    , "  gen f : [T] -> [T] @M;"
    , "  gen join : [T, T] -> [T] @M;"
    , "  gen wrap : [binder { } : [T]] -> [T] @M;"
    , "}"
    ]

require :: Either Text a -> IO a
require (Left err) = assertFailure (show err) >> fail "unreachable"
require (Right a) = pure a
