{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
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
import Strat.Poly.Doctrine
  ( Doctrine(..)
  , GenDecl(..)
  , deriveCtorTables
  , gdPlainDom
  , lookupCtorRefForOwnerInTables
  )
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Obj
  ( Obj(..)
  , ObjName(..)
  , ObjRef(..)
  , mkCon
  , ObjVar
  , pattern ObjVar
  , ovName
  , ovMode
  , tmVarToObjVar
  , ObjArg
  , pattern OAObj
  , pattern OATm
  )


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
        , "  mode M classifiedBy M via M.U_M;"
        , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
        , "  gen comp_var(a@M) : [a] -> [a] @M;"
        , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
        , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
        , "  gen U_M : [] -> [M.U_M] @M;"
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
  ctorTables <- case deriveCtorTables doc of
    Left err -> assertFailure (T.unpack err)
    Right tables -> pure tables
  listRef <- case lookupCtorRefForOwnerInTables doc ctorTables mode (ObjName "List") of
    Nothing -> assertFailure "expected List constructor in derived constructor table"
    Just ref -> pure ref
  gens <- case M.lookup mode (dGens doc) of
    Nothing -> assertFailure "expected generator table"
    Just g -> pure g
  nilGen <- case M.lookup (GenName "Nil") gens of
    Nothing -> assertFailure "expected Nil constructor"
    Just g -> pure g
  consGen <- case M.lookup (GenName "Cons") gens of
    Nothing -> assertFailure "expected Cons constructor"
    Just g -> pure g
  aVar <- case gdTyVars nilGen of
    [v] -> pure v
    _ -> assertFailure "expected Nil constructor to carry one type metavariable"
  let listTy = mkCon listRef [OAObj (OVar (tmVarToObjVar aVar))]
  gdPlainDom nilGen @?= []
  gdCod nilGen @?= [listTy]
  gdPlainDom consGen @?= [OVar (tmVarToObjVar aVar), listTy]
  gdCod consGen @?= [listTy]

testDataMacroCollision :: Assertion
testDataMacroCollision = do
  let src = T.unlines
        [ "doctrine D where {"
        , "  mode M classifiedBy M via M.U_M;"
        , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
        , "  gen comp_var(a@M) : [a] -> [a] @M;"
        , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
        , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
        , "  gen U_M : [] -> [M.U_M] @M;"
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
