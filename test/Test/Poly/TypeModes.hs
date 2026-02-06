{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.TypeModes
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import Strat.Poly.TypeExpr (TypeExpr(..), TypeName(..), TypeRef(..), TyVar(..))
import Strat.Poly.ModeTheory (ModeName(..), ModeTheory(..))
import Strat.Poly.Doctrine (Doctrine(..), TypeSig(..), validateDoctrine)
import Strat.Poly.DSL.Parse (parseDiagExpr)
import Strat.Poly.DSL.Elab (elabDiagExpr)
import Strat.Frontend.Env (emptyEnv)
import Strat.Poly.Diagram (diagramDom)
import Strat.Poly.UnifyTy (unifyTy)
import Strat.Poly.Graph (emptyDiagram, freshPort, validateDiagram)


tests :: TestTree
tests =
  testGroup
    "Poly.TypeModes"
    [ testCase "elaboration handles cross-mode nesting" testElabCrossMode
    , testCase "unqualified constructor ambiguity rejected" testAmbiguousConstructor
    , testCase "argument mode mismatch rejected" testArgModeMismatch
    , testCase "unify rejects mode mismatch" testUnifyModeMismatch
    , testCase "validateDiagram rejects port mode mismatch" testValidateDiagramModeMismatch
    ]

modeC :: ModeName
modeC = ModeName "C"

modeV :: ModeName
modeV = ModeName "V"

tvar :: ModeName -> Text -> TyVar
tvar mode name = TyVar { tvName = name, tvMode = mode }

tcon :: ModeName -> Text -> [TypeExpr] -> TypeExpr
tcon mode name args = TCon (TypeRef mode (TypeName name)) args

mkDoctrine :: [(ModeName, [(TypeName, TypeSig)])] -> Doctrine
mkDoctrine tables =
  Doctrine
    { dName = "D"
    , dModes = ModeTheory (S.fromList (map fst tables)) M.empty []
    , dTypes = M.fromList [ (mode, M.fromList types) | (mode, types) <- tables ]
    , dGens = M.empty
    , dCells2 = []
    , dAttrSorts = M.empty
    }

requireDoc :: Doctrine -> IO Doctrine
requireDoc doc =
  case validateDoctrine doc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure doc

testElabCrossMode :: Assertion
testElabCrossMode = do
  let doc0 =
        mkDoctrine
          [ (modeC, [(TypeName "A", TypeSig [])])
          , (modeV, [(TypeName "A", TypeSig []), (TypeName "Thunk", TypeSig [modeC])])
          ]
  doc <- requireDoc doc0
  raw <- case parseDiagExpr "id[V.Thunk(C.A)]" of
    Left err -> assertFailure (T.unpack err)
    Right expr -> pure expr
  diag <- case elabDiagExpr emptyEnv doc modeV [] raw of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  dom <- case diagramDom diag of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  dom @?= [tcon modeV "Thunk" [tcon modeC "A" []]]

testAmbiguousConstructor :: Assertion
testAmbiguousConstructor = do
  let doc0 =
        mkDoctrine
          [ (modeC, [(TypeName "A", TypeSig [])])
          , (modeV, [(TypeName "A", TypeSig [])])
          ]
  doc <- requireDoc doc0
  raw <- case parseDiagExpr "id[A]" of
    Left err -> assertFailure (T.unpack err)
    Right expr -> pure expr
  case elabDiagExpr emptyEnv doc modeC [] raw of
    Left err ->
      assertBool "expected ambiguity error" ("ambiguous" `T.isInfixOf` err)
    Right _ -> assertFailure "expected ambiguity error"

testArgModeMismatch :: Assertion
testArgModeMismatch = do
  let doc0 =
        mkDoctrine
          [ (modeC, [(TypeName "A", TypeSig [])])
          , (modeV, [(TypeName "A", TypeSig []), (TypeName "Thunk", TypeSig [modeC])])
          ]
  doc <- requireDoc doc0
  raw <- case parseDiagExpr "id[V.Thunk(V.A)]" of
    Left err -> assertFailure (T.unpack err)
    Right expr -> pure expr
  case elabDiagExpr emptyEnv doc modeV [] raw of
    Left err ->
      assertBool "expected argument mode mismatch" ("argument mode mismatch" `T.isInfixOf` err)
    Right _ -> assertFailure "expected argument mode mismatch"

testUnifyModeMismatch :: Assertion
testUnifyModeMismatch = do
  let aVar = tvar modeC "a"
  let aTy = tcon modeC "A" []
  case unifyTy (TVar aVar) aTy of
    Left err -> assertFailure (T.unpack err)
    Right _ -> pure ()
  case unifyTy (TVar aVar) (tcon modeV "B" []) of
    Left err ->
      assertBool "expected mode mismatch" ("mode mismatch" `T.isInfixOf` err)
    Right _ -> assertFailure "expected mode mismatch failure"

testValidateDiagramModeMismatch :: Assertion
testValidateDiagramModeMismatch = do
  let modeM = ModeName "M"
  let badTy = tcon modeC "A" []
  let (_p0, diag) = freshPort badTy (emptyDiagram modeM)
  case validateDiagram diag of
    Left err ->
      assertBool "expected port mode mismatch" ("wrong mode" `T.isInfixOf` err)
    Right _ -> assertFailure "expected validateDiagram to reject mode mismatch"
