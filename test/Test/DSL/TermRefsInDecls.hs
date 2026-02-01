{-# LANGUAGE OverloadedStrings #-}
module Test.DSL.TermRefsInDecls
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Map.Strict as M
import qualified Data.Text as T

import Strat.DSL.Parse (parseRawFile)
import Strat.DSL.Elab (elabRawFile, elabRawFileWithEnv)
import Strat.Frontend.Env (ModuleEnv(..), TermDef(..))
import Strat.Poly.Diagram (genD)
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.Names (GenName(..))
import Strat.Poly.TypeExpr (TypeExpr(..), TypeName(..), TypeRef(..))


tests :: TestTree
tests =
  testGroup
    "DSL.TermRefsInDecls"
    [ testCase "term ref in morphism RHS" testTermRefInMorphism
    ]

testTermRefInMorphism :: Assertion
testTermRefInMorphism = do
  baseEnv <- buildBaseEnv
  let src = T.unlines
        [ "morphism Id : D -> D where {"
        , "  gen f @M -> @t"
        , "}"
        ]
  case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFileWithEnv baseEnv rf of
        Left err -> assertFailure (T.unpack err)
        Right env ->
          assertBool "expected morphism Id" (M.member "Id" (meMorphisms env))

buildBaseEnv :: IO ModuleEnv
buildBaseEnv = do
  let src = T.unlines
        [ "doctrine D where {"
        , "  mode M;"
        , "  type A @M;"
        , "  gen f : [A] -> [A] @M;"
        , "}"
        ]
  env <- case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err)
        Right e -> pure e
  let mode = ModeName "M"
  let ty = TCon (TypeRef mode (TypeName "A")) []
  diag <- case genD mode [ty] [ty] (GenName "f") of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  let term = TermDef
        { tdDoctrine = "D"
        , tdMode = mode
        , tdDiagram = diag
        }
  pure env { meTerms = M.insert "t" term (meTerms env) }
