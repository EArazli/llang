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
import Strat.Poly.Obj (Obj(..), ObjName(..), ObjRef(..), mkCon)


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
        , "  mode M classifiedBy M via U_M;"
        , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
        , "  gen comp_var(a@M) : [a] -> [a] @M;"
        , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
        , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
        , "  gen U_M : [] -> [U_M] @M;"
        , "  gen A : [] -> [U_M] @M;"
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
  let ty = mkCon (ObjRef mode (ObjName "A")) []
  diag <- case genD mode [ty] [ty] (GenName "f") of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  let term = TermDef
        { tdDoctrine = "D"
        , tdMode = mode
        , tdDiagram = diag
        }
  pure env { meTerms = M.insert "t" term (meTerms env) }
