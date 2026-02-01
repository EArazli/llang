{-# LANGUAGE OverloadedStrings #-}
module Test.DSL.Effects
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Map.Strict as M
import qualified Data.Text as T

import Strat.DSL.Parse (parseRawFile)
import Strat.DSL.Elab (elabRawFile)
import Strat.Frontend.Env (meDoctrines, meMorphisms)
import Strat.Poly.Doctrine (Doctrine(..))
import Strat.Poly.Morphism (Morphism(..))


tests :: TestTree
tests =
  testGroup
    "DSL.Effects"
    [ testCase "effects empty extends base" testEffectsEmpty
    , testCase "effects singleton extends effect" testEffectsSingleton
    , testCase "effects multiple builds steps" testEffectsMultiple
    , testCase "effects fails when effect lacks fromBase" testEffectsMissingFromBase
    ]

testEffectsEmpty :: Assertion
testEffectsEmpty = do
  let src = T.unlines
        [ "doctrine Base where {"
        , "  mode M;"
        , "}"
        , "doctrine Combined = effects Base { };"
        ]
  env <- case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err)
        Right e -> pure e
  assertBool "expected Combined doctrine" (M.member "Combined" (meDoctrines env))
  case M.lookup "Combined.fromBase" (meMorphisms env) of
    Nothing -> assertFailure "expected Combined.fromBase"
    Just _ -> pure ()

testEffectsSingleton :: Assertion
testEffectsSingleton = do
  let src = T.unlines
        [ "doctrine Base where {"
        , "  mode M;"
        , "}"
        , "doctrine E1 extends Base where {"
        , "}"
        , "doctrine Combined = effects Base { E1 };"
        ]
  env <- case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err)
        Right e -> pure e
  case M.lookup "Combined.fromBase" (meMorphisms env) of
    Nothing -> assertFailure "expected Combined.fromBase"
    Just mor -> dName (morSrc mor) @?= "E1"

testEffectsMultiple :: Assertion
testEffectsMultiple = do
  let src = T.unlines
        [ "doctrine Base where {"
        , "  mode M;"
        , "}"
        , "doctrine E1 extends Base where {}"
        , "doctrine E2 extends Base where {}"
        , "doctrine E3 extends Base where {}"
        , "doctrine Combined = effects Base { E1, E2, E3 };"
        ]
  env <- case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err)
        Right e -> pure e
  assertBool "expected Combined__step1 doctrine" (M.member "Combined__step1" (meDoctrines env))
  assertBool "expected Combined__step2 doctrine" (M.member "Combined__step2" (meDoctrines env))
  assertBool "expected Combined doctrine" (M.member "Combined" (meDoctrines env))
  assertBool "expected Combined__step1.glue" (M.member "Combined__step1.glue" (meMorphisms env))
  assertBool "expected Combined__step2.glue" (M.member "Combined__step2.glue" (meMorphisms env))

testEffectsMissingFromBase :: Assertion
testEffectsMissingFromBase = do
  let src = T.unlines
        [ "doctrine Base where {"
        , "  mode M;"
        , "}"
        , "doctrine E1 where {"
        , "  mode M;"
        , "}"
        , "doctrine E2 extends Base where {}"
        , "doctrine Combined = effects Base { E1, E2 };"
        ]
  case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertBool "expected missing fromBase error" ("E1.fromBase" `T.isInfixOf` err)
        Right _ -> assertFailure "expected effects to fail"
