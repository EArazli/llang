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
    [ testCase "derived transform requires acyclic mode" testDerivedRequiresAcyclic
    , testCase "old fragment role syntax is rejected" testOldFragmentSyntaxRejected
    , testCase "old letgraph syntax is rejected" testOldLetgraphSyntaxRejected
    , testCase "old quote policy syntax is rejected" testOldQuotePolicyRejected
    , testCase "included generators quote to let_ constructors" testIncludedQuoted
    , testCase "omitted generators quote to res_ constructors" testResidualQuoted
    , testCase "cross binders false leaves nested syntax residual" testCrossBindersFalse
    , testCase "cross binders true recursively quotes nested syntax" testCrossBindersTrue
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
      , transformerDecl
      , "fragment Share in D mode M where {"
      , "  gen f = share;"
      , "}"
      ]
    )
    "share"


testOldLetgraphSyntaxRejected :: Assertion
testOldLetgraphSyntaxRejected =
  assertParseFails
    (T.unlines
      [ baseDoctrine
      , transformerDecl
      , "fragment Share in D mode M where {"
      , "  include gen f;"
      , "}"
      , "derived doctrine D_Share = letgraph Share;"
      ]
    )
    "letgraph"


testOldQuotePolicyRejected :: Assertion
testOldQuotePolicyRejected =
  assertParseFails
    (T.unlines
      [ baseDoctrine
      , transformerDecl
      , "fragment Share in D mode M where {"
      , "  include gen f;"
      , "}"
      , "derived doctrine D_Share = transform explicit_sharing using Share;"
      , "pipeline p where {"
      , "  quote into D_Share with { naming = \"boundary_labels_first\"; };"
      , "}"
      ]
    )
    "with"


testIncludedQuoted :: Assertion
testIncludedQuoted = do
  result <- runNamed includedQuoteProgram "main"
  let out = prOutput result
  assertBool "expected quoted let_f edge" ("let_f" `T.isInfixOf` out)
  assertBool "did not expect residual f edge" (not ("res_f" `T.isInfixOf` out))


testResidualQuoted :: Assertion
testResidualQuoted = do
  result <- runNamed residualQuoteProgram "main"
  let out = prOutput result
  assertBool "expected quoted residual f edge" ("res_f" `T.isInfixOf` out)
  assertBool "did not expect let_f edge" (not ("let_f" `T.isInfixOf` out))


testCrossBindersFalse :: Assertion
testCrossBindersFalse = do
  result <- runNamed binderResidualProgram "main"
  let out = prOutput result
  assertBool "expected residual nested a edge" ("res_a" `T.isInfixOf` out)
  assertBool "did not expect nested let_a edge" (not ("let_a" `T.isInfixOf` out))


testCrossBindersTrue :: Assertion
testCrossBindersTrue = do
  result <- runNamed binderIncludedProgram "main"
  let out = prOutput result
  assertBool "expected nested let_a edge" ("let_a" `T.isInfixOf` out)


runNamed :: Text -> Text -> IO RunResult
runNamed src runName = do
  env <- require (elabProgram src)
  runDef <- require (selectRun env (Just runName))
  require (runWithEnv env runDef)


assertParseFails :: Text -> Text -> Assertion
assertParseFails src needle =
  case parseRawFile src of
    Left err ->
      assertBool "expected parse failure to mention deleted syntax" (needle `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected parse failure"


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
    , transformerDecl
    , "fragment Share in D mode M where {"
    , "  include gen a;"
    , "}"
    , "derived doctrine D_Share = transform explicit_sharing using Share;"
    ]


includedQuoteProgram :: Text
includedQuoteProgram =
  mkQuoteProgram
    [ "include gen a;"
    , "include gen f;"
    ]
    "a; f"


residualQuoteProgram :: Text
residualQuoteProgram =
  mkQuoteProgram
    [ "include gen a;"
    ]
    "a; f"


binderResidualProgram :: Text
binderResidualProgram =
  mkQuoteProgram
    [ "include gen a;"
    , "cross binders = false;"
    ]
    "wrap[a]"


binderIncludedProgram :: Text
binderIncludedProgram =
  mkQuoteProgram
    [ "include gen a;"
    , "cross binders = true;"
    ]
    "wrap[a]"


mkQuoteProgram :: [Text] -> Text -> Text
mkQuoteProgram fragmentItems exprText =
  T.unlines
    ( [ baseDoctrine
      , transformerDecl
      , "fragment Share in D mode M where {"
      ]
        <> map ("  " <>) fragmentItems
        <> [ "}"
           , "derived doctrine D_Share = transform explicit_sharing using Share;"
           , "pipeline p where {"
           , "  quote into D_Share;"
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
    , "  gen wrap : [binder { } : [T]] -> [T] @M;"
    , "}"
    ]


transformerDecl :: Text
transformerDecl =
  T.unlines
    [ "transformer explicit_sharing where {"
    , "  source doctrine D;"
    , "  source mode M;"
    , "  source fragment F;"
    , "  copy doctrine D;"
    , "  emit object CtxNil;"
    , "  emit object CtxCons(a@M, g@M);"
    , "  emit object Ref(a@M);"
    , "  emit object Refs(g@M);"
    , "  emit object Prog(gIn@M, gOut@M);"
    , "  emit utility input_refs;"
    , "  emit utility refs_nil;"
    , "  emit utility refs_cons;"
    , "  emit utility refs_head;"
    , "  emit utility refs_tail;"
    , "  emit utility dup_refs;"
    , "  emit utility drop_refs;"
    , "  emit utility return_refs;"
    , "  emit utility residual_box;"
    , "  emit utility residual_feedback;"
    , "  for included generator g in F {"
    , "    emit binding prefix \"let_\";"
    , "  }"
    , "  for excluded generator g in D mode M relative to F {"
    , "    emit residual prefix \"res_\";"
    , "  }"
    , "}"
    ]


require :: Either Text a -> IO a
require (Left err) = assertFailure (show err) >> fail "unreachable"
require (Right a) = pure a
