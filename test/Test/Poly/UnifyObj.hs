{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
module Test.Poly.UnifyObj
  ( tests
  ) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit
import qualified Data.Set as S
import Data.Text (isInfixOf)
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.Obj
  ( ObjName(..)
  , ObjRef(..)
  , ObjVar
  , pattern ObjVar
  , ovName
  , ovMode
  , pattern OATm
  , TermDiagram(..)
  , pattern OVar
  , mkCon
  , freeObjVarsObj
  , occursObjVar
  )
import Strat.Poly.Diagram (idDTm)
import Strat.Poly.TypeTheory (modeOnlyTypeTheory)
import Test.Poly.Helpers (mkModes)
import qualified Strat.Poly.UnifyObj as U


tests :: TestTree
tests =
  testGroup
    "Poly.UnifyObj"
    [ testCase "object vars in term arguments are visible to free/occurs checks" testSeesObjVarInTermArg
    , testCase "unified substitution rejects code/term kind collisions" testRejectsMetaKindCollision
    , testCase "scope-0 code metavariables reject bound term indices in object bindings" testRejectsCodeMetaScopeEscape
    ]

testSeesObjVarInTermArg :: Assertion
testSeesObjVarInTermArg = do
  let mode = ModeName "M"
      aVar = ObjVar { ovName = "a", ovMode = mode }
      fooRef = ObjRef mode (ObjName "Foo")
      tm = TermDiagram (idDTm mode [OVar aVar] [OVar aVar])
      rhs = mkCon fooRef [OATm tm]
  assertBool "free vars should include object vars from CATm payloads" (aVar `S.member` freeObjVarsObj rhs)
  assertBool "occurs check should include object vars from CATm payloads" (occursObjVar aVar rhs)

testRejectsMetaKindCollision :: Assertion
testRejectsMetaKindCollision = do
  let mode = ModeName "M"
      v = ObjVar { ovName = "x", ovMode = mode }
      rhsObj = OVar v
      rhsTm = TermDiagram (idDTm mode [] [])
      assertKindMismatch result =
        case result of
          Left err ->
            assertBool
              "expected a kind mismatch error"
              ("kind mismatch" `isInfixOf` err)
          Right _ ->
            assertFailure "expected insertion to fail with kind mismatch"
  substCodeFirst <- case U.insertCodeMeta v rhsObj U.emptySubst of
    Left err -> assertFailure ("unexpected insertCodeMeta failure: " <> show err) >> pure U.emptySubst
    Right s -> pure s
  assertKindMismatch (U.insertTmMeta v rhsTm substCodeFirst)
  substTmFirst <- case U.insertTmMeta v rhsTm U.emptySubst of
    Left err -> assertFailure ("unexpected insertTmMeta failure: " <> show err) >> pure U.emptySubst
    Right s -> pure s
  assertKindMismatch (U.insertCodeMeta v rhsObj substTmFirst)

testRejectsCodeMetaScopeEscape :: Assertion
testRejectsCodeMetaScopeEscape = do
  let mode = ModeName "M"
      tt = modeOnlyTypeTheory (mkModes [mode])
      v = ObjVar { ovName = "x", ovMode = mode }
      sortTy = mkCon (ObjRef mode (ObjName "S")) []
      fooRef = ObjRef mode (ObjName "Foo")
      tm = TermDiagram (idDTm mode [sortTy] [sortTy])
      rhs = mkCon fooRef [OATm tm]
  case U.unifyObjFlex tt [sortTy] (S.singleton v) U.emptySubst (OVar v) rhs of
    Left err ->
      assertBool
        "expected code-meta scope escape error"
        ("scope-0 code metavariable" `isInfixOf` err)
    Right _ ->
      assertFailure "expected unification to reject scope-0 code metavariable binding with bound indices"
