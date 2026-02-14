{-# LANGUAGE OverloadedStrings #-}
module Test.DSL.Templates
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Map.Strict as M
import qualified Data.Text as T

import Strat.DSL.Parse (parseRawFile)
import Strat.DSL.Elab (elabRawFile)
import Strat.Frontend.Env (meDoctrines, meMorphisms)
import Strat.Frontend.Run (RunResult(..), runWithEnv, selectRun)
import Strat.Poly.Doctrine (Doctrine(..))
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.Names (GenName(..))
import Strat.Poly.TypeExpr (TypeName(..))


tests :: TestTree
tests =
  testGroup
    "DSL.Templates"
    [ testCase "instantiate substitutes identifiers" testInstantiateSubst
    , testCase "multiple instantiations do not collide" testInstantiateMultiple
    , testCase "run over instantiated doctrine" testInstantiateRun
    ]

testInstantiateSubst :: Assertion
testInstantiateSubst = do
  let src = T.unlines
        [ "doctrine Base where {"
        , "  mode BaseM;"
        , "}"
        , "doctrine_template Temp(BaseDoc, ModeX, TyName, GenName) where {"
        , "  doctrine Temp extends BaseDoc where {"
        , "    mode ModeX;"
        , "    type TyName @ModeX;"
        , "    gen GenName : [TyName] -> [TyName] @ModeX;"
        , "  }"
        , "}"
        , "doctrine Inst = instantiate Temp(Base, M, Box, flip);"
        ]
  env <- case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err)
        Right e -> pure e
  doc <- case M.lookup "Inst" (meDoctrines env) of
    Nothing -> assertFailure "expected Inst doctrine"
    Just d -> pure d
  let mode = ModeName "M"
  types <- case M.lookup mode (dTypes doc) of
    Nothing -> assertFailure "expected mode table"
    Just t -> pure t
  assertBool "expected Box type" (M.member (TypeName "Box") types)
  gens <- case M.lookup mode (dGens doc) of
    Nothing -> assertFailure "expected generator table"
    Just g -> pure g
  assertBool "expected flip generator" (M.member (GenName "flip") gens)
  case M.lookup "Inst.fromBase" (meMorphisms env) of
    Nothing -> assertFailure "expected Inst.fromBase morphism"
    Just _ -> pure ()

testInstantiateMultiple :: Assertion
testInstantiateMultiple = do
  let src = T.unlines
        [ "doctrine Base where {"
        , "  mode BaseM;"
        , "}"
        , "doctrine_template Temp(BaseDoc, TyName) where {"
        , "  doctrine Temp extends BaseDoc where {"
        , "    mode M;"
        , "    type TyName @M;"
        , "  }"
        , "}"
        , "doctrine Inst1 = instantiate Temp(Base, Box);"
        , "doctrine Inst2 = instantiate Temp(Base, Crate);"
        ]
  env <- case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err)
        Right e -> pure e
  assertBool "expected Inst1" (M.member "Inst1" (meDoctrines env))
  assertBool "expected Inst2" (M.member "Inst2" (meDoctrines env))

testInstantiateRun :: Assertion
testInstantiateRun = do
  let src = T.unlines
        [ "doctrine Base where {"
        , "  mode M;"
        , "  type A @M;"
        , "  gen f : [A] -> [A] @M;"
        , "}"
        , "doctrine_template Wrap(BaseDoc) where {"
        , "  doctrine Wrap extends BaseDoc where {"
        , "  }"
        , "}"
        , "doctrine Inst = instantiate Wrap(Base);"
        , "pipeline p where {"
        , "  normalize;"
        , "  extract diagram;"
        , "}"
        , "run main using p where {"
        , "  source doctrine Inst;"
        , "  source mode M;"
        , "} ---"
        , "f"
        ]
  env <- case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err)
        Right e -> pure e
  spec <- case selectRun env Nothing of
    Left err -> assertFailure (T.unpack err)
    Right s -> pure s
  result <- case runWithEnv env spec of
    Left err -> assertFailure (T.unpack err)
    Right r -> pure r
  prOutput result @?=
    T.intercalate "\n"
      [ "mode: M"
      , "ixctx: []"
      , "in: [p0:M.A]"
      , "out: [p1:M.A]"
      , "edges:"
      , "  e0: f [p0] -> [p1]"
      ]
