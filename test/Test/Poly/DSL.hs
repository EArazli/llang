{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.DSL
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Kernel.DSL.Parse (parseRawFile)
import Strat.Kernel.DSL.Elab (elabRawFile)
import Strat.Frontend.Env (mePolyDoctrines, mePolyMorphisms, ModuleEnv(..))
import Strat.Poly.DSL.Parse (parseDiagExpr)
import Strat.Poly.DSL.Elab (elabDiagExpr)
import Strat.Poly.ModeTheory (ModeName(..), ModeTheory(..))
import Strat.Poly.Doctrine
import Strat.Poly.Names (GenName(..))
import Strat.Poly.TypeExpr (TypeExpr(..), TypeName(..))
import Strat.Poly.Rewrite (rulesFromDoctrine, rewriteOnce)
import Strat.Poly.Normalize (normalize, NormalizationStatus(..))
import Strat.Poly.Pretty (renderDiagram)
import Strat.Poly.Morphism (checkMorphism)
import Paths_llang (getDataFileName)


tests :: TestTree
tests =
  testGroup
    "Poly.DSL"
    [ testCase "parse/elab monoid doctrine and normalize" testPolyDSLNormalize
    , testCase "polymorphism declared in example file" testPolyMorphismDSL
    , testCase "polydoctrine extends produces fromBase morphism" testPolyFromBaseMorphism
    , testCase "poly pushout renames gen types" testPolyPushoutRenamesTypes
    ]

testPolyDSLNormalize :: Assertion
testPolyDSLNormalize = do
  let src = T.unlines
        [ "polydoctrine Monoid where {"
        , "  mode M;"
        , "  type A @M;"
        , "  gen unit : [] -> [A] @M;"
        , "  gen mul : [A, A] -> [A] @M;"
        , "  rule computational assoc -> : [A, A, A] -> [A] @M ="
        , "    (mul * id[A]) ; mul == (id[A] * mul) ; mul"
        , "}"
        ]
  env <- case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err)
        Right e -> pure e
  doc <- case M.lookup "Monoid" (mePolyDoctrines env) of
    Nothing -> assertFailure "expected Monoid polydoctrine"
    Just d -> pure d
  mode <- case S.toList (mtModes (dModes doc)) of
    [m] -> pure m
    _ -> assertFailure "expected single mode"
  rawExpr <- case parseDiagExpr "(mul * id[A]) ; mul" of
    Left err -> assertFailure (T.unpack err)
    Right e -> pure e
  diag <- case elabDiagExpr doc mode [] rawExpr of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  let rules = rulesFromDoctrine doc
  norm <- case normalize 10 rules diag of
    Left err -> assertFailure (T.unpack err)
    Right r -> pure r
  case norm of
    Finished d -> do
      -- normalization should agree with a single rewrite step
      step <- case rewriteOnce rules diag of
        Left err -> assertFailure (T.unpack err)
        Right r -> pure r
      case step of
        Nothing -> assertFailure "expected a rewrite step"
        Just expected -> do
          got <- case renderDiagram d of
            Left err -> assertFailure (T.unpack err)
            Right txt -> pure txt
          want <- case renderDiagram expected of
            Left err -> assertFailure (T.unpack err)
            Right txt -> pure txt
          got @?= want
    OutOfFuel _ -> assertFailure "expected normalization to finish"

testPolyMorphismDSL :: Assertion
testPolyMorphismDSL = do
  path <- getDataFileName "examples/poly/monoid_to_string.llang"
  src <- TIO.readFile path
  env <- case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err)
        Right e -> pure e
  case M.lookup "MonoidToString" (mePolyMorphisms env) of
    Nothing -> assertFailure "expected polymorphism MonoidToString"
    Just _ -> pure ()

testPolyFromBaseMorphism :: Assertion
testPolyFromBaseMorphism = do
  let src = T.unlines
        [ "polydoctrine Base where {"
        , "  mode M;"
        , "  type A @M;"
        , "  gen f : [A] -> [A] @M;"
        , "}"
        , "polydoctrine Ext extends Base where {"
        , "  gen g : [A] -> [A] @M;"
        , "}"
        ]
  env <- case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err)
        Right e -> pure e
  mor <- case M.lookup "Ext.fromBase" (mePolyMorphisms env) of
    Nothing -> assertFailure "expected polymorphism Ext.fromBase"
    Just m -> pure m
  case checkMorphism mor of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()

testPolyPushoutRenamesTypes :: Assertion
testPolyPushoutRenamesTypes = do
  let src = T.unlines
        [ "polydoctrine Base where {"
        , "  mode M;"
        , "}"
        , "polydoctrine Left extends Base where {"
        , "  type A @M;"
        , "  gen f : [A] -> [A] @M;"
        , "}"
        , "polydoctrine Right extends Base where {"
        , "  type B @M;"
        , "  gen g : [B] -> [B] @M;"
        , "}"
        , "polydoctrine Push = pushout Left.fromBase Right.fromBase;"
        ]
  env <- case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err)
        Right e -> pure e
  doc <- case M.lookup "Push" (mePolyDoctrines env) of
    Nothing -> assertFailure "expected Push polydoctrine"
    Just d -> pure d
  let mode = ModeName "M"
  types <- case M.lookup mode (dTypes doc) of
    Nothing -> assertFailure "expected type table for mode M"
    Just t -> pure t
  assertBool "expected Left_inl_A type" (M.member (TypeName "Left_inl_A") types)
  assertBool "expected Right_inr_B type" (M.member (TypeName "Right_inr_B") types)
  gens <- case M.lookup mode (dGens doc) of
    Nothing -> assertFailure "expected generator table for mode M"
    Just g -> pure g
  genLeft <- case M.lookup (GenName "Left_inl_f") gens of
    Nothing -> assertFailure "expected Left_inl_f generator"
    Just g -> pure g
  let leftTy = TCon (TypeName "Left_inl_A") []
  gdDom genLeft @?= [leftTy]
  gdCod genLeft @?= [leftTy]
