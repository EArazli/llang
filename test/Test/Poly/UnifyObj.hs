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
  , mkModeMetaVar
  , TmVar(..)
  , CodeTerm(..)
  , pattern OAObj
  , pattern OATm
  , TermDiagram(..)
  , pattern OVar
  , mkCon
  , freeVarsObj
  , occursVar
  )
import Strat.Poly.Diagram (idDTm)
import Strat.Poly.TermExpr (TermExpr(..), termExprToDiagram, diagramToTermExpr)
import Strat.Poly.Graph (Diagram(..), emptyDiagram, freshPort, addEdgePayload, validateDiagram, EdgePayload(..))
import Strat.Poly.TypeTheory (TypeTheory(..), TypeParamSig(..), modeOnlyTypeTheory)
import Test.Poly.Helpers (mkModes)
import qualified Strat.Poly.UnifyObj as U


tests :: TestTree
tests =
  testGroup
    "Poly.UnifyObj"
    [ testCase "object vars in term arguments are visible to free/occurs checks" testSeesObjVarInTermArg
    , testCase "unified substitution rejects cross-category collisions" testSeparateMetaNamespaces
    , testCase "substitution keys remain distinct across owner modes" testSubstKeySeparatesOwnerModes
    , testCase "normalizeSubst prunes term identity bindings" testNormalizeSubstTermIdentity
    , testCase "composeSubst rejects mixed-category collisions" testComposeSubstCategoryConflict
    , testCase "scope-0 code metavariables reject bound term indices in object bindings" testRejectsCodeMetaScopeEscape
    , testCase "expandModSpine handles nested CTLift using inner source owner" testExpandModSpineNestedOwner
    , testCase "expandModSpine rejects CTLift owner/target mismatch" testExpandModSpineOwnerMismatch
    , testCase "unification under CTLift with non-identity path binds inner metavariables" testUnifyUnderCTLiftPathBindsMeta
    , testCase "unification under CTLift binds inner metavariables" testUnifyUnderCTLiftBindsMeta
    , testCase "code metavariable scope uses classifier slice of term context" testCodeMetaScopeClassifierSlice
    , testCase "non-canonical injective term-meta spine solve succeeds" testPatternSolveNonCanonicalInjective
    , testCase "solved term metas instantiate at arbitrary spines" testPatternSubstituteArbitrarySpine
    , testCase "non-injective term-meta solving spine is rejected" testPatternRejectNonInjectiveSolve
    , testCase "term-meta arity mismatch is rejected at term and graph boundaries" testPatternArityMismatchRejected
    ]

buildClassifiedModes :: ModeName -> ModeName -> Either Text ModeTheory
buildClassifiedModes ty tm = do
  mt0 <- addMode ty emptyModeTheory
  mt1 <- addMode tm mt0
  let uTy = OVar (mkModeMetaVar "U_Ty" ty)
  mt2 <-
    addClassification
      ty
      ClassificationDecl
        { cdClassifier = ty
        , cdUniverse = uTy
        
        , cdComp = Nothing
        }
      mt1
  let uTm = OVar (mkModeMetaVar "U_Tm" ty)
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
      aVar = mkModeMetaVar "a" mode
      fooRef = ObjRef mode (ObjName "Foo")
      tm = TermDiagram (idDTm mode [OVar aVar] [OVar aVar])
      rhs = mkCon fooRef [OATm tm]
  assertBool "free vars should include object vars from CATm payloads" (aVar `S.member` freeVarsObj rhs)
  assertBool "occurs check should include object vars from CATm payloads" (occursVar aVar rhs)

testSeparateMetaNamespaces :: Assertion
testSeparateMetaNamespaces = do
  let mode = ModeName "M"
      v = mkModeMetaVar "x" mode
      rhsObj = OVar v
      rhsObj2 = mkCon (ObjRef mode (ObjName "T")) []
      rhsTm = TermDiagram (idDTm mode [] [])
  substCodeFirst <- case U.insertCodeMeta v rhsObj U.emptySubst of
    Left err -> assertFailure ("unexpected insertCodeMeta failure: " <> show err) >> pure U.emptySubst
    Right s -> pure s
  case U.insertTmMeta v rhsTm substCodeFirst of
    Left _ -> pure ()
    Right _ -> assertFailure "expected term insert after type insert to fail with category conflict"
  substTmFirst <- case U.insertTmMeta v rhsTm U.emptySubst of
    Left err -> assertFailure ("unexpected insertTmMeta failure: " <> show err) >> pure U.emptySubst
    Right s -> pure s
  case U.insertCodeMeta v rhsObj substTmFirst of
    Left _ -> pure ()
    Right _ -> assertFailure "expected type insert after term insert to fail with category conflict"
  substOverwrite <- case U.insertCodeMeta v rhsObj U.emptySubst of
    Left err -> assertFailure ("unexpected insertCodeMeta failure: " <> show err) >> pure U.emptySubst
    Right s -> pure s
  substOverwrite2 <- case U.insertCodeMeta v rhsObj2 substOverwrite of
    Left err -> assertFailure ("unexpected overwrite failure: " <> show err) >> pure U.emptySubst
    Right s -> pure s
  U.lookupCodeMeta substOverwrite2 v @?= Just rhsObj2
  U.lookupTmMeta substOverwrite2 v @?= Nothing

testSubstKeySeparatesOwnerModes :: Assertion
testSubstKeySeparatesOwnerModes = do
  let modeA = ModeName "A"
      modeB = ModeName "B"
      vA = mkModeMetaVar "x" modeA
      vB = mkModeMetaVar "x" modeB
      rhsA = mkCon (ObjRef modeA (ObjName "TA")) []
      rhsB = mkCon (ObjRef modeB (ObjName "TB")) []
  subst <- case U.mkSubst [(vA, OAObj rhsA), (vB, OAObj rhsB)] of
    Left err -> assertFailure ("unexpected mkSubst failure: " <> show err) >> pure U.emptySubst
    Right s -> pure s
  length (U.codeBindings subst) @?= 2
  U.lookupCodeMeta subst vA @?= Just rhsA
  U.lookupCodeMeta subst vB @?= Just rhsB

testNormalizeSubstTermIdentity :: Assertion
testNormalizeSubstTermIdentity = do
  let mode = ModeName "M"
      tt = modeOnlyTypeTheory (mkModes [mode])
      sortTy = mkCon (ObjRef mode (ObjName "A")) []
      v =
        TmVar
          { tmvName = "x"
          , tmvSort = sortTy
          , tmvScope = 0
          , tmvOwnerMode = Just mode
          }
  tmId <- either (assertFailure . show) pure (termExprToDiagram tt [] sortTy (TMMeta v []))
  subst0 <- case U.mkSubst [(v, OATm tmId)] of
    Left err -> assertFailure ("unexpected mkSubst failure: " <> show err) >> pure U.emptySubst
    Right s -> pure s
  subst <- case U.normalizeSubst tt subst0 of
    Left err -> assertFailure ("unexpected normalizeSubst failure: " <> show err) >> pure U.emptySubst
    Right s -> pure s
  U.tmBindings subst @?= []

testComposeSubstCategoryConflict :: Assertion
testComposeSubstCategoryConflict = do
  let mode = ModeName "M"
      tt = modeOnlyTypeTheory (mkModes [mode])
      sortTy = mkCon (ObjRef mode (ObjName "A")) []
      v =
        TmVar
          { tmvName = "x"
          , tmvSort = sortTy
          , tmvScope = 0
          , tmvOwnerMode = Just mode
          }
      rhsObj = mkCon (ObjRef mode (ObjName "T")) []
  rhsTm <- either (assertFailure . show) pure (termExprToDiagram tt [] sortTy (TMMeta v []))
  substObj <- case U.mkSubst [(v, OAObj rhsObj)] of
    Left err -> assertFailure ("unexpected object mkSubst failure: " <> show err) >> pure U.emptySubst
    Right s -> pure s
  substTm <- case U.mkSubst [(v, OATm rhsTm)] of
    Left err -> assertFailure ("unexpected term mkSubst failure: " <> show err) >> pure U.emptySubst
    Right s -> pure s
  case U.composeSubst tt substTm substObj of
    Left _ -> pure ()
    Right _ -> assertFailure "expected composeSubst to reject mixed-category collision (tm over obj)"
  case U.composeSubst tt substObj substTm of
    Left _ -> pure ()
    Right _ -> assertFailure "expected composeSubst to reject mixed-category collision (obj over tm)"

testRejectsCodeMetaScopeEscape :: Assertion
testRejectsCodeMetaScopeEscape = do
  let mode = ModeName "M"
      tt = modeOnlyTypeTheory (mkModes [mode])
      v = mkModeMetaVar "x" mode
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
      aVar = mkModeMetaVar "a" modeA
      me = ModExpr { meSrc = modeA, meTgt = modeB, mePath = [modF] }
      lhs = Obj { objOwnerMode = modeB, objCode = CTLift me (objCode (OVar aVar)) }
      rhs = Obj { objOwnerMode = modeB, objCode = CTLift me (objCode (mkCon (ObjRef modeA (ObjName "Unit")) [])) }
  mt <- either (assertFailure . show) pure $
    addModDecl ModDecl { mdName = modF, mdSrc = modeA, mdTgt = modeB } (mkModes [modeA, modeB])
  let tt = modeOnlyTypeTheory mt
  subst <- case U.unifyObjFlex tt [] (S.singleton (aVar)) U.emptySubst lhs rhs of
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
      aVar = mkModeMetaVar "a" modeTm
      liftId = ModExpr { meSrc = modeTy, meTgt = modeTy, mePath = [] }
      lhs = Obj { objOwnerMode = modeTm, objCode = CTLift liftId (objCode (OVar aVar)) }
      rhs = Obj { objOwnerMode = modeTm, objCode = CTLift liftId (objCode (mkCon (ObjRef modeTy (ObjName "UnitTy")) [])) }
  mt <- either (assertFailure . show) pure (buildClassifiedModes modeTy modeTm)
  let tt = modeOnlyTypeTheory mt
  subst <- case U.unifyObjFlex tt [] (S.singleton (aVar)) U.emptySubst lhs rhs of
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
      baseMeta = mkModeMetaVar "x" modeTm
      baseMetaTm = baseMeta
      vClassifier = baseMetaTm { tmvName = "x_classifier", tmvScope = 1 }
      vOwner = baseMetaTm { tmvName = "x_owner", tmvScope = 1 }
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
  case U.unifyObjFlex tt tmCtx (S.singleton vClassifier) U.emptySubst (OVar vClassifier) boxTyObj of
    Left err ->
      assertFailure ("expected classifier-slice binding to succeed: " <> show err)
    Right _ -> pure ()
  case U.unifyObjFlex tt tmCtx (S.singleton vOwner) U.emptySubst (OVar vOwner) boxTmObj of
    Left err ->
      assertBool
        "expected classifier-slice escape rejection"
        ("escape from bound term-variable scope" `isInfixOf` err)
    Right _ ->
      assertFailure "expected owner-slice bound index to be rejected for classifier-scoped code metavariable"

testPatternSolveNonCanonicalInjective :: Assertion
testPatternSolveNonCanonicalInjective = do
  let mode = ModeName "M"
      tt = modeOnlyTypeTheory (mkModes [mode])
      sortTy = mkCon (ObjRef mode (ObjName "A")) []
      tmCtx = [sortTy, sortTy, sortTy]
      x =
        TmVar
          { tmvName = "x"
          , tmvSort = sortTy
          , tmvScope = 2
          , tmvOwnerMode = Just mode
          }
  lhs <- either (assertFailure . show) pure (termExprToDiagram tt tmCtx sortTy (TMMeta x [1, 0]))
  rhs <- either (assertFailure . show) pure (termExprToDiagram tt tmCtx sortTy (TMBound 1))
  subst <- case U.unifyTm tt tmCtx (S.singleton x) U.emptySubst sortTy lhs rhs of
    Left err -> assertFailure ("expected non-canonical injective solve to succeed: " <> show err) >> pure U.emptySubst
    Right s -> pure s
  tmBinding <-
    case U.lookupTmMeta subst x of
      Nothing -> assertFailure "expected solved term-meta binding" >> pure (TermDiagram (idDTm mode [] []))
      Just tm -> pure tm
  expr <- either (assertFailure . show) pure (diagramToTermExpr tt tmCtx sortTy tmBinding)
  expr @?= TMBound 0

testPatternSubstituteArbitrarySpine :: Assertion
testPatternSubstituteArbitrarySpine = do
  let mode = ModeName "M"
      tt = modeOnlyTypeTheory (mkModes [mode])
      sortTy = mkCon (ObjRef mode (ObjName "A")) []
      tmCtx = [sortTy, sortTy, sortTy]
      x =
        TmVar
          { tmvName = "x"
          , tmvSort = sortTy
          , tmvScope = 2
          , tmvOwnerMode = Just mode
          }
  seedL <- either (assertFailure . show) pure (termExprToDiagram tt tmCtx sortTy (TMMeta x [1, 0]))
  seedR <- either (assertFailure . show) pure (termExprToDiagram tt tmCtx sortTy (TMBound 1))
  seedSubst <- case U.unifyTm tt tmCtx (S.singleton x) U.emptySubst sortTy seedL seedR of
    Left err -> assertFailure ("expected seed solve to succeed: " <> show err) >> pure U.emptySubst
    Right s -> pure s
  query <- either (assertFailure . show) pure (termExprToDiagram tt tmCtx sortTy (TMMeta x [2, 0]))
  want <- either (assertFailure . show) pure (termExprToDiagram tt tmCtx sortTy (TMBound 2))
  case U.unifyTm tt tmCtx S.empty seedSubst sortTy query want of
    Left err ->
      assertFailure
        ( "expected solved meta to instantiate at non-canonical spine; got: "
            <> show err
        )
    Right _ ->
      pure ()

testPatternRejectNonInjectiveSolve :: Assertion
testPatternRejectNonInjectiveSolve = do
  let mode = ModeName "M"
      tt = modeOnlyTypeTheory (mkModes [mode])
      sortTy = mkCon (ObjRef mode (ObjName "A")) []
      tmCtx = [sortTy, sortTy]
      x =
        TmVar
          { tmvName = "x"
          , tmvSort = sortTy
          , tmvScope = 2
          , tmvOwnerMode = Just mode
          }
  case termExprToDiagram tt tmCtx sortTy (TMMeta x [0, 0]) of
    Left err ->
      assertBool
        ("expected non-injective spine rejection, got: " <> show err)
        ("duplicate ports" `isInfixOf` err)
    Right _ ->
      assertFailure "expected non-injective term-meta spine to be rejected"

testPatternArityMismatchRejected :: Assertion
testPatternArityMismatchRejected = do
  let mode = ModeName "M"
      tt = modeOnlyTypeTheory (mkModes [mode])
      sortTy = mkCon (ObjRef mode (ObjName "A")) []
      v =
        TmVar
          { tmvName = "m"
          , tmvSort = sortTy
          , tmvScope = 1
          , tmvOwnerMode = Just mode
          }
  case termExprToDiagram tt [sortTy] sortTy (TMMeta v []) of
    Left err ->
      assertBool
        ("expected term-level spine arity rejection, got: " <> show err)
        ("spine arity mismatch" `isInfixOf` err)
    Right _ ->
      assertFailure "expected termExprToDiagram to reject mismatched spine arity"

  let (inPid, d0) = freshPort sortTy (emptyDiagram mode [])
      (outPid, d1) = freshPort sortTy d0
  d2 <- either (assertFailure . show) pure (addEdgePayload (PTmMeta v) [] [outPid] d1)
  let badDiag = d2 { dIn = [inPid], dOut = [outPid] }
  case validateDiagram badDiag of
    Left err ->
      assertBool
        ("expected graph-level PTmMeta arity rejection, got: " <> show err)
        ("PTmMeta arity mismatch" `isInfixOf` err)
    Right _ ->
      assertFailure "expected validateDiagram to reject PTmMeta arity mismatch"

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
