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
    [ testCase "derived reflected quotation requires acyclic mode" testDerivedRequiresAcyclic
    , testCase "old fragment role syntax is rejected" testOldFragmentSyntaxRejected
    , testCase "old transform-derived syntax is rejected" testOldTransformDerivedSyntaxRejected
    , testCase "old quote policy syntax is rejected" testOldQuotePolicyRejected
    , testCase "extract JS is rejected as an unsupported host extractor" testExtractJsRejected
    , testCase "included generators are shared in reflected output" testIncludedQuoted
    , testCase "excluded generators stay duplicated in reflected output" testResidualQuoted
    , testCase "cross binders false leaves nested sharing disabled" testCrossBindersFalse
    , testCase "cross binders true recursively shares nested bindings" testCrossBindersTrue
    ]


testDerivedRequiresAcyclic :: Assertion
testDerivedRequiresAcyclic =
  case elabProgram nonAcyclicProgram of
    Left err ->
      assertBool "expected acyclic-mode rejection" ("acyclic" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected elaboration to reject non-acyclic derived doctrine"


testOldFragmentSyntaxRejected :: Assertion
testOldFragmentSyntaxRejected =
  assertParseFails
    (T.unlines
      [ baseDoctrine
      , "fragment Share in D mode M where {"
      , "  gen f = share;"
      , "}"
      ]
    )


testOldTransformDerivedSyntaxRejected :: Assertion
testOldTransformDerivedSyntaxRejected =
  assertParseFails
    (T.unlines
      [ baseDoctrine
      , "fragment Share in D mode M where {"
      , "  include gen f;"
      , "}"
      , "derived doctrine D_Q = transform explicit_sharing using Share;"
      ]
    )


testOldQuotePolicyRejected :: Assertion
testOldQuotePolicyRejected =
  assertParseFails
    (T.unlines
      [ baseDoctrine
      , "fragment Share in D mode M where {"
      , "  include gen f;"
      , "}"
      , "derived doctrine D_Q = reflect quotation of D mode M;"
      , "pipeline p where {"
      , "  quote into D_Q with { naming = \"boundary_labels_first\"; };"
      , "}"
      ]
    )


testExtractJsRejected :: Assertion
testExtractJsRejected =
  case elabProgram src of
    Left err ->
      assertBool "expected unsupported extractor rejection" ("unsupported extractor doctrine JS" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected elaboration to reject extract JS"
  where
    src =
      T.unlines
        [ baseDoctrine
        , "fragment Share in D mode M where {"
        , "  include gen a;"
        , "}"
        , "derived doctrine D_Q = reflect quotation of D mode M;"
        , "pipeline p where {"
        , "  quote using Share into D_Q;"
        , "  extract JS { stdout = true; };"
        , "}"
        ]


testIncludedQuoted :: Assertion
testIncludedQuoted = do
  result <- runNamed includedQuoteProgram "main"
  let out = prOutput result
  assertEqual "expected one shared q_a binding" 1 (countOccurrences "q_a" out)
  assertEqual "expected one shared q_f binding" 1 (countOccurrences "q_f" out)
  assertBool "expected reflected q_begin" ("q_begin" `T.isInfixOf` out)
  assertBool "expected reflected RefIds encoding" ("refIds_cons" `T.isInfixOf` out)
  assertBool "expected reflected q_end" ("q_end" `T.isInfixOf` out)


testResidualQuoted :: Assertion
testResidualQuoted = do
  result <- runNamed residualQuoteProgram "main"
  let out = prOutput result
  assertEqual "expected one shared q_a binding" 1 (countOccurrences "q_a" out)
  assertEqual "expected duplicated q_f bindings" 2 (countOccurrences "q_f" out)


testCrossBindersFalse :: Assertion
testCrossBindersFalse = do
  result <- runNamed binderResidualProgram "main"
  let out = prOutput result
  assertEqual "expected nested q_a duplication" 2 (countOccurrences "q_a" out)
  assertEqual "expected nested q_f duplication" 2 (countOccurrences "q_f" out)
  assertBool "expected reflected wrap binding" ("q_wrap" `T.isInfixOf` out)


testCrossBindersTrue :: Assertion
testCrossBindersTrue = do
  result <- runNamed binderIncludedProgram "main"
  let out = prOutput result
  assertEqual "expected nested q_a sharing" 1 (countOccurrences "q_a" out)
  assertEqual "expected nested q_f sharing" 1 (countOccurrences "q_f" out)
  assertBool "expected reflected wrap binding" ("q_wrap" `T.isInfixOf` out)


runNamed :: Text -> Text -> IO RunResult
runNamed src runName = do
  env <- require (elabProgram src)
  runDef <- require (selectRun env (Just runName))
  require (runWithEnv env runDef)


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


mkQuoteProgram :: [Text] -> Text -> Text
mkQuoteProgram fragmentItems exprText =
  T.unlines
    ( [ baseDoctrine
      , "fragment Share in D mode M where {"
      ]
        <> map ("  " <>) fragmentItems
        <> [ "}"
           , "derived doctrine D_Q = reflect quotation of D mode M;"
           , "pipeline p where {"
           , "  quote using Share into D_Q;"
           , "  extract diagram;"
           , "}"
           , "run main using p where {"
           , "  source doctrine D;"
           , "  source mode M;"
           , "}"
           , "---"
           , exprText
           , "---"
           ]
    )


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
