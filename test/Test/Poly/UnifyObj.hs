{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
module Test.Poly.UnifyObj
  ( tests
  ) where

import Control.Monad (foldM)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Text (isInfixOf)
import Strat.Poly.ModeTheory
  ( ModeName(..)
  , ModName(..)
  , ModExpr(..)
  , ModDecl(..)
  , ClassificationDecl(..)
  , emptyModeTheory
  , addMode
  , addModDecl
  , addClassification
  )
import Strat.Poly.Obj
  ( ObjName(..)
  , ObjRef(..)
  , Obj(Obj, objOwnerMode, objCode)
  , ObjVar
  , pattern ObjVar
  , ovName
  , ovMode
  , TmVar(..)
  , CodeTerm(..)
  , pattern OATm
  , TermDiagram(..)
  , pattern OVar
  , mkCon
  , freeObjVarsObj
  , occursObjVar
  )
import Strat.Poly.Diagram (idDTm)
import Strat.Poly.TermExpr (TermExpr(..), termExprToDiagram)
import Strat.Poly.TypeTheory (TypeTheory(..), TypeParamSig(..), modeOnlyTypeTheory)
import Test.Poly.Helpers (mkModes)
import qualified Strat.Poly.UnifyObj as U


tests :: TestTree
tests =
  testGroup
    "Poly.UnifyObj"
    [ testCase "object vars in term arguments are visible to free/occurs checks" testSeesObjVarInTermArg
    , testCase "unified substitution rejects code/term kind collisions" testRejectsMetaKindCollision
    , testCase "scope-0 code metavariables reject bound term indices in object bindings" testRejectsCodeMetaScopeEscape
    , testCase "expandModSpine handles nested CTMod using inner source owner" testExpandModSpineNestedOwner
    , testCase "expandModSpine rejects CTMod owner/target mismatch" testExpandModSpineOwnerMismatch
    , testCase "code metavariable scope uses classifier slice of term context" testCodeMetaScopeClassifierSlice
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

testExpandModSpineNestedOwner :: Assertion
testExpandModSpineNestedOwner = do
  let modeA = ModeName "A"
      modeB = ModeName "B"
      modeC = ModeName "C"
      modF = ModName "f"
      modH = ModName "h"
      innerBase = mkCon (ObjRef modeC (ObjName "BaseC")) []
      innerA = Obj { objOwnerMode = modeA, objCode = CTMod ModExpr { meSrc = modeC, meTgt = modeA, mePath = [modH] } (objCode innerBase) }
      outer =
        Obj
          { objOwnerMode = modeB
          , objCode = CTMod ModExpr { meSrc = modeA, meTgt = modeB, mePath = [modF] } (objCode innerA)
          }
  mt <- either (assertFailure . show) pure $
    foldM
      (\acc decl -> addModDecl decl acc)
      (mkModes [modeA, modeB, modeC])
      [ ModDecl { mdName = modF, mdSrc = modeA, mdTgt = modeB }
      , ModDecl { mdName = modH, mdSrc = modeC, mdTgt = modeA }
      ]
  let tt = modeOnlyTypeTheory mt
  case U.unifyObjFlex tt [] S.empty U.emptySubst outer outer of
    Left err -> assertFailure ("expected nested CTMod unification to succeed: " <> show err)
    Right _ -> pure ()

testExpandModSpineOwnerMismatch :: Assertion
testExpandModSpineOwnerMismatch = do
  let modeA = ModeName "A"
      modeB = ModeName "B"
      modF = ModName "f"
      baseA = mkCon (ObjRef modeA (ObjName "BaseA")) []
      badOuter =
        Obj
          { objOwnerMode = modeA
          , objCode = CTMod ModExpr { meSrc = modeA, meTgt = modeB, mePath = [modF] } (objCode baseA)
          }
  mt <- either (assertFailure . show) pure $
    addModDecl ModDecl { mdName = modF, mdSrc = modeA, mdTgt = modeB } (mkModes [modeA, modeB])
  let tt = modeOnlyTypeTheory mt
  case U.unifyObjFlex tt [] S.empty U.emptySubst badOuter badOuter of
    Left err ->
      assertBool
        "expected owner/target mismatch error from CTMod spine expansion"
        ("modality target does not match object owner mode" `isInfixOf` err)
    Right _ ->
      assertFailure "expected malformed CTMod owner/target mismatch to be rejected"

testCodeMetaScopeClassifierSlice :: Assertion
testCodeMetaScopeClassifierSlice = do
  let modeTy = ModeName "Ty"
      modeTm = ModeName "Tm"
      natTy = mkCon (ObjRef modeTy (ObjName "Nat")) []
      idxTm = mkCon (ObjRef modeTm (ObjName "Idx")) []
      boxTyRef = ObjRef modeTm (ObjName "BoxTyIdx")
      boxTmRef = ObjRef modeTm (ObjName "BoxTmIdx")
      baseMeta = ObjVar { ovName = "x", ovMode = modeTm }
      vClassifier = baseMeta { tmvName = "x_classifier", tmvScope = 1 }
      vOwner = baseMeta { tmvName = "x_owner", tmvScope = 1 }
      tmCtx = [natTy, idxTm]
  mt <- either (assertFailure . show) pure (buildClassifiedModes modeTy modeTm)
  let tt =
        (modeOnlyTypeTheory mt)
          { ttObjParams =
              M.fromList
                [ (boxTyRef, [TPS_Tm natTy])
                , (boxTmRef, [TPS_Tm idxTm])
                ]
          }
  tmTyIdx <- either (assertFailure . show) pure (termExprToDiagram tt tmCtx natTy (TMBound 0))
  tmOwnerIdx <- either (assertFailure . show) pure (termExprToDiagram tt tmCtx idxTm (TMBound 1))
  case U.unifyObjFlex tt tmCtx (S.singleton vClassifier) U.emptySubst (OVar vClassifier) (mkCon boxTyRef [OATm tmTyIdx]) of
    Left err ->
      assertFailure ("expected classifier-slice binding to succeed: " <> show err)
    Right _ -> pure ()
  case U.unifyObjFlex tt tmCtx (S.singleton vOwner) U.emptySubst (OVar vOwner) (mkCon boxTmRef [OATm tmOwnerIdx]) of
    Left err ->
      assertBool
        "expected classifier-slice escape rejection"
        ("escape from bound term-variable scope" `isInfixOf` err)
    Right _ ->
      assertFailure "expected owner-slice bound index to be rejected for classifier-scoped code metavariable"
  where
    buildClassifiedModes ty tm = do
      mt0 <- addMode ty emptyModeTheory
      mt1 <- addMode tm mt0
      let uTy = OVar ObjVar { ovName = "U_Ty", ovMode = ty }
      mt2 <-
        addClassification
          ty
          ClassificationDecl
            { cdClassifier = ty
            , cdUniverse = uTy
            , cdTag = Nothing
            , cdComp = Nothing
            }
          mt1
      let uTm = OVar ObjVar { ovName = "U_Tm", ovMode = ty }
      addClassification
        tm
        ClassificationDecl
          { cdClassifier = ty
          , cdUniverse = uTm
          , cdTag = Nothing
          , cdComp = Nothing
          }
        mt2
