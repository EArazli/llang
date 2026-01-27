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
import Strat.Frontend.Env (mePolyDoctrines, ModuleEnv(..))
import Strat.Poly.DSL.Parse (parseDiagExpr)
import Strat.Poly.DSL.Elab (elabDiagExpr)
import Strat.Poly.ModeTheory (ModeName(..), ModeTheory(..))
import Strat.Poly.Doctrine
import Strat.Poly.Rewrite (rulesFromDoctrine, rewriteOnce)
import Strat.Poly.Normalize (normalize, NormalizationStatus(..))
import Strat.Poly.Pretty (renderDiagram)
import Paths_llang (getDataFileName)


tests :: TestTree
tests =
  testGroup
    "Poly.DSL"
    [ testCase "parse/elab monoid doctrine and normalize" testPolyDSLNormalize
    , testCase "polymorphism declared in example file" testPolyMorphismDSL
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
