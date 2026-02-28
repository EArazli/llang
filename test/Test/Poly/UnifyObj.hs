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
import Data.Text (Text, isInfixOf)
import Strat.Poly.ModeTheory
  ( ModeName(..)
  , ModName(..)
  , ModExpr(..)
  , ModDecl(..)
  , ModeTheory
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
  , objVarToTmVar
  , tmVarToObjVar
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
    , testCase "unified substitution keeps code and term metas in separate maps" testSeparateMetaNamespaces
    , testCase "scope-0 code metavariables reject bound term indices in object bindings" testRejectsCodeMetaScopeEscape
    , testCase "expandModSpine handles nested CTLift using inner source owner" testExpandModSpineNestedOwner
    , testCase "expandModSpine rejects CTLift owner/target mismatch" testExpandModSpineOwnerMismatch
    , testCase "unification under CTLift with non-identity path binds inner metavariables" testUnifyUnderCTLiftPathBindsMeta
    , testCase "unification under CTLift binds inner metavariables" testUnifyUnderCTLiftBindsMeta
    , testCase "code metavariable scope uses classifier slice of term context" testCodeMetaScopeClassifierSlice
    ]

buildClassifiedModes :: ModeName -> ModeName -> Either Text ModeTheory
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
        
        , cdComp = Nothing
        }
      mt1
  let uTm = OVar ObjVar { ovName = "U_Tm", ovMode = ty }
  addClassification
    tm
    ClassificationDecl
      { cdClassifier = ty
      , cdUniverse = uTm
      
      , cdComp = Nothing
      }
    mt2

testSeesObjVarInTermArg :: Assertion
testSeesObjVarInTermArg = do
  let mode = ModeName "M"
      aVar = ObjVar { ovName = "a", ovMode = mode }
      fooRef = ObjRef mode (ObjName "Foo")
      tm = TermDiagram (idDTm mode [OVar aVar] [OVar aVar])
      rhs = mkCon fooRef [OATm tm]
  assertBool "free vars should include object vars from CATm payloads" (aVar `S.member` freeObjVarsObj rhs)
  assertBool "occurs check should include object vars from CATm payloads" (occursObjVar aVar rhs)

testSeparateMetaNamespaces :: Assertion
testSeparateMetaNamespaces = do
  let mode = ModeName "M"
      v = ObjVar { ovName = "x", ovMode = mode }
      rhsObj = OVar v
      rhsTm = TermDiagram (idDTm mode [] [])
  substCodeFirst <- case U.insertCodeMeta v rhsObj U.emptySubst of
    Left err -> assertFailure ("unexpected insertCodeMeta failure: " <> show err) >> pure U.emptySubst
    Right s -> pure s
  substBoth <- case U.insertTmMeta (objVarToTmVar v) rhsTm substCodeFirst of
    Left err -> assertFailure ("unexpected insertTmMeta failure: " <> show err) >> pure U.emptySubst
    Right s -> pure s
  U.lookupCodeMeta substBoth v @?= Just rhsObj
  U.lookupTmMeta substBoth (objVarToTmVar v) @?= Just rhsTm
  substTmFirst <- case U.insertTmMeta (objVarToTmVar v) rhsTm U.emptySubst of
    Left err -> assertFailure ("unexpected insertTmMeta failure: " <> show err) >> pure U.emptySubst
    Right s -> pure s
  substBoth2 <- case U.insertCodeMeta v rhsObj substTmFirst of
    Left err -> assertFailure ("unexpected insertCodeMeta failure: " <> show err) >> pure U.emptySubst
    Right s -> pure s
  U.lookupCodeMeta substBoth2 v @?= Just rhsObj
  U.lookupTmMeta substBoth2 (objVarToTmVar v) @?= Just rhsTm

testRejectsCodeMetaScopeEscape :: Assertion
testRejectsCodeMetaScopeEscape = do
  let mode = ModeName "M"
      tt = modeOnlyTypeTheory (mkModes [mode])
      v = ObjVar { ovName = "x", ovMode = mode }
      sortTy = mkCon (ObjRef mode (ObjName "S")) []
      fooRef = ObjRef mode (ObjName "Foo")
      tm = TermDiagram (idDTm mode [sortTy] [sortTy])
      rhs = mkCon fooRef [OATm tm]
  case U.unifyObjFlex tt [sortTy] (S.singleton (objVarToTmVar v)) U.emptySubst (OVar v) rhs of
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
      innerA = Obj { objOwnerMode = modeA, objCode = CTLift ModExpr { meSrc = modeC, meTgt = modeA, mePath = [modH] } (objCode innerBase) }
      outer =
        Obj
          { objOwnerMode = modeB
          , objCode = CTLift ModExpr { meSrc = modeA, meTgt = modeB, mePath = [modF] } (objCode innerA)
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
    Left err -> assertFailure ("expected nested CTLift unification to succeed: " <> show err)
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
          , objCode = CTLift ModExpr { meSrc = modeA, meTgt = modeB, mePath = [modF] } (objCode baseA)
          }
  mt <- either (assertFailure . show) pure $
    addModDecl ModDecl { mdName = modF, mdSrc = modeA, mdTgt = modeB } (mkModes [modeA, modeB])
  let tt = modeOnlyTypeTheory mt
  case U.unifyObjFlex tt [] S.empty U.emptySubst badOuter badOuter of
    Left err ->
      assertBool
        "expected code-mode/target mismatch error from CTLift spine expansion"
        ( "modality target" `isInfixOf` err
            || "current code mode" `isInfixOf` err
            || "cannot unify" `isInfixOf` err
        )
    Right _ ->
      assertFailure "expected malformed CTLift owner/target mismatch to be rejected"

testUnifyUnderCTLiftPathBindsMeta :: Assertion
testUnifyUnderCTLiftPathBindsMeta = do
  let modeA = ModeName "A"
      modeB = ModeName "B"
      modF = ModName "f"
      aVar = ObjVar { ovName = "a", ovMode = modeA }
      me = ModExpr { meSrc = modeA, meTgt = modeB, mePath = [modF] }
      lhs = Obj { objOwnerMode = modeB, objCode = CTLift me (objCode (OVar aVar)) }
      rhs = Obj { objOwnerMode = modeB, objCode = CTLift me (objCode (mkCon (ObjRef modeA (ObjName "Unit")) [])) }
  mt <- either (assertFailure . show) pure $
    addModDecl ModDecl { mdName = modF, mdSrc = modeA, mdTgt = modeB } (mkModes [modeA, modeB])
  let tt = modeOnlyTypeTheory mt
  subst <- case U.unifyObjFlex tt [] (S.singleton (objVarToTmVar aVar)) U.emptySubst lhs rhs of
    Left err -> assertFailure ("expected CTLift unification to succeed: " <> show err) >> pure U.emptySubst
    Right s -> pure s
  case U.lookupCodeMeta subst aVar of
    Just bound ->
      bound @?= mkCon (ObjRef modeA (ObjName "Unit")) []
    Nothing ->
      assertFailure "expected unification to bind the inner code metavariable under CTLift"

testUnifyUnderCTLiftBindsMeta :: Assertion
testUnifyUnderCTLiftBindsMeta = do
  let modeTy = ModeName "Ty"
      modeTm = ModeName "Tm"
      aVar = ObjVar { ovName = "a", ovMode = modeTm }
      liftId = ModExpr { meSrc = modeTy, meTgt = modeTy, mePath = [] }
      lhs = Obj { objOwnerMode = modeTm, objCode = CTLift liftId (objCode (OVar aVar)) }
      rhs = Obj { objOwnerMode = modeTm, objCode = CTLift liftId (objCode (mkCon (ObjRef modeTy (ObjName "UnitTy")) [])) }
  mt <- either (assertFailure . show) pure (buildClassifiedModes modeTy modeTm)
  let tt = modeOnlyTypeTheory mt
  subst <- case U.unifyObjFlex tt [] (S.singleton (objVarToTmVar aVar)) U.emptySubst lhs rhs of
    Left err -> assertFailure ("expected CTLift unification to succeed: " <> show err) >> pure U.emptySubst
    Right s -> pure s
  case U.lookupCodeMeta subst aVar of
    Just bound ->
      bound @?= Obj { objOwnerMode = modeTm, objCode = CTCon (ObjRef modeTy (ObjName "UnitTy")) [] }
    Nothing ->
      assertFailure "expected unification to bind the inner code metavariable under CTLift"

testCodeMetaScopeClassifierSlice :: Assertion
testCodeMetaScopeClassifierSlice = do
  let modeTy = ModeName "Ty"
      modeTm = ModeName "Tm"
      natTy = mkCon (ObjRef modeTy (ObjName "Nat")) []
      idxTm = Obj { objOwnerMode = modeTm, objCode = CTCon (ObjRef modeTy (ObjName "Idx")) [] }
      boxTyRef = ObjRef modeTy (ObjName "BoxTyIdx")
      boxTmRef = ObjRef modeTy (ObjName "BoxTmIdx")
      baseMeta = ObjVar { ovName = "x", ovMode = modeTm }
      baseMetaTm = objVarToTmVar baseMeta
      vClassifier = tmVarToObjVar (baseMetaTm { tmvName = "x_classifier", tmvScope = 1 })
      vOwner = tmVarToObjVar (baseMetaTm { tmvName = "x_owner", tmvScope = 1 })
      tmCtx = [natTy, idxTm]
  mt <- either (assertFailure . show) pure (buildClassifiedModes modeTy modeTm)
  let tt =
        withCtorSigs
          (modeOnlyTypeTheory mt)
          [ (boxTyRef, [TPS_Tm natTy])
          , (boxTmRef, [TPS_Tm idxTm])
          ]
  tmTyIdx <- either (assertFailure . show) pure (termExprToDiagram tt tmCtx natTy (TMBound 0))
  tmOwnerIdx <- either (assertFailure . show) pure (termExprToDiagram tt tmCtx idxTm (TMBound 1))
  let boxTyObj = Obj { objOwnerMode = modeTm, objCode = CTCon boxTyRef [OATm tmTyIdx] }
  let boxTmObj = Obj { objOwnerMode = modeTm, objCode = CTCon boxTmRef [OATm tmOwnerIdx] }
  case U.unifyObjFlex tt tmCtx (S.singleton (objVarToTmVar vClassifier)) U.emptySubst (OVar vClassifier) boxTyObj of
    Left err ->
      assertFailure ("expected classifier-slice binding to succeed: " <> show err)
    Right _ -> pure ()
  case U.unifyObjFlex tt tmCtx (S.singleton (objVarToTmVar vOwner)) U.emptySubst (OVar vOwner) boxTmObj of
    Left err ->
      assertBool
        "expected classifier-slice escape rejection"
        ("escape from bound term-variable scope" `isInfixOf` err)
    Right _ ->
      assertFailure "expected owner-slice bound index to be rejected for classifier-scoped code metavariable"

withCtorSigs :: TypeTheory -> [(ObjRef, [TypeParamSig])] -> TypeTheory
withCtorSigs tt entries =
  tt
    { ttCtorSigs = table
    , ttUniverseCtors = M.map (S.fromList . M.keys) table
    }
  where
    table =
      foldl
        (\acc (ref, sig) -> M.insertWith M.union (orMode ref) (M.singleton (orName ref) sig) acc)
        M.empty
        entries
