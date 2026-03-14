{-# LANGUAGE OverloadedStrings #-}
module Test.DSL.TermRefsInDecls
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Map.Strict as M
import qualified Data.Text as T

import Strat.DSL.Parse (parseRawFile)
import Strat.DSL.Elab (elabRawFileWithEnv)
import Strat.Frontend.Env (ModuleEnv(..), emptyEnv)
import Strat.Frontend.Prelude (preludeDoctrines)


tests :: TestTree
tests =
  testGroup
    "DSL.TermRefsInDecls"
    [ testCase "module values can reference prior declarations by bare name" testModuleValueRef
    , testCase "legacy @value syntax is rejected" testLegacyValueRefRejected
    ]


testModuleValueRef :: Assertion
testModuleValueRef = do
  let src =
        T.unlines
          [ "module_surface DocUnit where {"
          , "  doctrine Doc;"
          , "  mode Doc;"
          , "}"
          , "language DocLang where {"
          , "  doctrine Doc;"
          , "  module_surface DocUnit;"
          , "}"
          , "module Greeting in DocLang where {"
          , "  let hello"
          , "  ---"
          , "  text(\"hello\")"
          , "  ---"
          , "  let main"
          , "  ---"
          , "  (hello * text(\"!\")); cat"
          , "  ---"
          , "  export { main };"
          , "}"
          ]
  env <- requireRight (elabProgram src)
  assertBool "expected compiled module" (M.member "Greeting" (meModules env))


testLegacyValueRefRejected :: Assertion
testLegacyValueRefRejected =
  case parseRawFile src of
    Left _ -> pure ()
    Right _ -> assertFailure "expected legacy @value syntax to be rejected"
  where
    src =
      T.unlines
        [ "module_surface DocUnit where {"
        , "  doctrine Doc;"
        , "  mode Doc;"
        , "}"
        , "language DocLang where {"
        , "  doctrine Doc;"
        , "  module_surface DocUnit;"
        , "}"
        , "module Greeting in DocLang where {"
        , "  let hello"
        , "  ---"
        , "  text(\"hello\")"
        , "  ---"
        , "  let main"
        , "  ---"
        , "  (@hello * text(\"!\")); cat"
        , "  ---"
        , "  export { main };"
        , "}"
        ]


elabProgram :: T.Text -> Either T.Text ModuleEnv
elabProgram src = do
  raw <- parseRawFile src
  elabRawFileWithEnv env0 raw
  where
    env0 = emptyEnv { meDoctrines = preludeDoctrines }


requireRight :: Either T.Text a -> IO a
requireRight res =
  case res of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right x -> pure x
