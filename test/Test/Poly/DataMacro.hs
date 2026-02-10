{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.DataMacro
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Map.Strict as M
import qualified Data.Text as T

import Strat.DSL.Parse (parseRawFile)
import Strat.DSL.Elab (elabRawFile)
import Strat.Frontend.Env (meDoctrines)
import Strat.Poly.Doctrine (Doctrine(..), GenDecl(..), gdPlainDom)
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.Names (GenName(..))
import Strat.Poly.TypeExpr (TypeExpr(..), TypeName(..), TypeRef(..), TyVar(..), TypeArg(..))


tests :: TestTree
tests =
  testGroup
    "Poly.DataMacro"
    [ testCase "data macro expands to constructors" testDataMacroElab
    , testCase "data macro rejects constructor collision" testDataMacroCollision
    ]

testDataMacroElab :: Assertion
testDataMacroElab = do
  let src = T.unlines
        [ "doctrine D where {"
        , "  mode M;"
        , "  data List (a@M) @M where {"
        , "    Nil : [];"
        , "    Cons : [a, List(a)];"
        , "  }"
        , "}"
        ]
  env <- case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err)
        Right e -> pure e
  doc <- case M.lookup "D" (meDoctrines env) of
    Nothing -> assertFailure "expected doctrine D"
    Just d -> pure d
  let mode = ModeName "M"
  types <- case M.lookup mode (dTypes doc) of
    Nothing -> assertFailure "expected type table"
    Just t -> pure t
  assertBool "expected List type" (M.member (TypeName "List") types)
  gens <- case M.lookup mode (dGens doc) of
    Nothing -> assertFailure "expected generator table"
    Just g -> pure g
  nilGen <- case M.lookup (GenName "Nil") gens of
    Nothing -> assertFailure "expected Nil constructor"
    Just g -> pure g
  consGen <- case M.lookup (GenName "Cons") gens of
    Nothing -> assertFailure "expected Cons constructor"
    Just g -> pure g
  let aVar = TyVar { tvName = "a", tvMode = mode }
  let listTy = TCon (TypeRef mode (TypeName "List")) [TAType (TVar aVar)]
  gdPlainDom nilGen @?= []
  gdCod nilGen @?= [listTy]
  gdPlainDom consGen @?= [TVar aVar, listTy]
  gdCod consGen @?= [listTy]

testDataMacroCollision :: Assertion
testDataMacroCollision = do
  let src = T.unlines
        [ "doctrine D where {"
        , "  mode M;"
        , "  gen Nil : [] -> [] @M;"
        , "  data List (a@M) @M where {"
        , "    Nil : [];"
        , "  }"
        , "}"
        ]
  case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertBool "expected constructor collision" ("constructor name conflicts" `T.isInfixOf` err)
        Right _ -> assertFailure "expected data macro to fail"
