{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.Rewrite
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.Diagram
import Strat.Poly.Graph
import Strat.Poly.Names (GenName(..), BoxName(..))
import Strat.Poly.TypeExpr (TypeExpr(..), TypeName(..), TypeRef(..), TyVar(..))
import Strat.Poly.Rewrite
import Strat.Poly.Normalize (normalize, NormalizationStatus(..))
import Strat.Poly.Match (Match(..), findFirstMatchNoDoc, findFirstMatchWithTyVarsNoDoc)
import Strat.Poly.UnifyTy (Subst(..))
import Strat.Poly.ModeTheory (ModeName(..), ModeTheory, ModName(..), ModDecl(..), ModExpr(..), ModEqn(..), addMode, addModDecl, addModEqn)
import Strat.Poly.TypeTheory (TypeTheory, modeOnlyTypeTheory)
import Strat.Poly.Pretty (renderDiagram)
import qualified Data.IntMap.Strict as IM
import Test.Poly.Helpers (mkModes)


tests :: TestTree
tests =
  testGroup
    "Poly.Rewrite"
    [ testCase "simple local rewrite" testSimpleRewrite
    , testCase "subdiagram rewrite across composition" testSubdiagramRewrite
    , testCase "dangling condition rejects match" testDanglingReject
    , testCase "matching requires injective host mapping" testInjectiveMatch
    , testCase "non-injective match does not trigger rewrite" testNonInjectiveRewrite
    , testCase "rewrite inside box" testRewriteInsideBox
    , testCase "box mismatch rejects" testBoxMismatchRejects
    , testCase "box match accepts" testBoxMatchAccepts
    , testCase "nested boxes match" testNestedBoxesMatch
    , testCase "type vars unify through boxes" testBoxTypeVarUnify
    , testCase "rewrite uses mode equations during substitution" testRewriteUsesModeEq
    , testCase "normalize deterministic" testNormalizeDeterminism
    ]

modeName :: ModeName
modeName = ModeName "M"

aTy :: TypeExpr
aTy = TCon (TypeRef modeName (TypeName "A")) []

tvar :: Text -> TyVar
tvar name = TyVar { tvName = name, tvMode = modeName }

mkGen :: Text -> [TypeExpr] -> [TypeExpr] -> Either Text Diagram
mkGen name dom cod = genD modeName dom cod (GenName name)

require :: Either Text a -> IO a
require = either (assertFailure . T.unpack) pure

mkTypeTheory :: ModeTheory -> TypeTheory
mkTypeTheory = modeOnlyTypeTheory

assocRule :: Either Text RewriteRule
assocRule = do
  mul <- mkGen "mul" [aTy, aTy] [aTy]
  id1 <- pure (idD modeName [aTy])
  left <- tensorD mul id1
  lhs <- compD (mkModes [modeName]) mul left
  right <- tensorD id1 mul
  rhs <- compD (mkModes [modeName]) mul right
  pure RewriteRule
    { rrName = "assoc"
    , rrLHS = lhs
    , rrRHS = rhs
    , rrTyVars = []
    , rrIxVars = []
    }

testSimpleRewrite :: Assertion
testSimpleRewrite = do
  rule <- either (assertFailure . T.unpack) pure assocRule
  let lhs = rrLHS rule
  let mt = mkModes [modeName]
  res <- case rewriteOnce (mkTypeTheory mt) [rule] lhs of
    Left err -> assertFailure (T.unpack err)
    Right r -> pure r
  case res of
    Nothing -> assertFailure "expected rewrite"
    Just d -> do
      got <- require (renderDiagram d)
      expected <- require (renderDiagram (rrRHS rule))
      got @?= expected

testSubdiagramRewrite :: Assertion
testSubdiagramRewrite = do
  rule <- either (assertFailure . T.unpack) pure assocRule
  let lhs = rrLHS rule
  extra <- require (mkGen "mul" [aTy, aTy] [aTy])
  host <- require (tensorD lhs extra)
  let mt = mkModes [modeName]
  res <- case rewriteOnce (mkTypeTheory mt) [rule] host of
    Left err -> assertFailure (T.unpack err)
    Right r -> pure r
  case res of
    Nothing -> assertFailure "expected subdiagram rewrite"
    Just _ -> pure ()

testDanglingReject :: Assertion
testDanglingReject = do
  f <- require (mkGen "f" [aTy] [aTy])
  g <- require (mkGen "g" [aTy] [aTy])
  lhs <- require (compD (mkModes [modeName]) g f)
  let rhs = lhs
  let rule = RewriteRule
        { rrName = "dangling"
        , rrLHS = lhs
        , rrRHS = rhs
        , rrTyVars = []
        , rrIxVars = []
        }
  extra <- require (mkGen "h" [aTy] [aTy])
  host0 <- require (tensorD lhs extra)
  let boundary = dIn lhs <> dOut lhs
  let internalPort = head (filter (`notElem` boundary) (diagramPortIds lhs))
  let host1 = host0 { dOut = internalPort : dOut host0 }
  let mt = mkModes [modeName]
  res <- case rewriteOnce (mkTypeTheory mt) [rule] host1 of
    Left err -> assertFailure (T.unpack err)
    Right r -> pure r
  case res of
    Nothing -> pure ()
    Just _ -> assertFailure "expected dangling match rejection"

testInjectiveMatch :: Assertion
testInjectiveMatch = do
  g <- require (mkGen "f" [aTy] [aTy])
  pat <- require (tensorD g g)
  let host = g
  res <- case findFirstMatchNoDoc pat host of
    Left err -> assertFailure (T.unpack err)
    Right m -> pure m
  case res of
    Nothing -> pure ()
    Just _ -> assertFailure "expected no match due to non-injective mapping"

testNonInjectiveRewrite :: Assertion
testNonInjectiveRewrite = do
  g <- require (mkGen "f" [aTy] [aTy])
  lhs <- require (tensorD g g)
  let rule = RewriteRule
        { rrName = "dup"
        , rrLHS = lhs
        , rrRHS = lhs
        , rrTyVars = []
        , rrIxVars = []
        }
  let mt = mkModes [modeName]
  res <- case rewriteOnce (mkTypeTheory mt) [rule] g of
    Left err -> assertFailure (T.unpack err)
    Right r -> pure r
  case res of
    Nothing -> pure ()
    Just _ -> assertFailure "expected no rewrite due to non-injective match"

testRewriteInsideBox :: Assertion
testRewriteInsideBox = do
  f <- require (mkGen "f" [aTy] [aTy])
  g <- require (mkGen "g" [aTy] [aTy])
  let rule = RewriteRule
        { rrName = "boxrule"
        , rrLHS = f
        , rrRHS = g
        , rrTyVars = []
        , rrIxVars = []
        }
  let (inP, d0) = freshPort aTy (emptyDiagram modeName [])
  let (outP, d1) = freshPort aTy d0
  let boxEdge = PBox (BoxName "B") f
  d2 <- require (addEdgePayload boxEdge [inP] [outP] d1)
  let host = d2 { dIn = [inP], dOut = [outP] }
  let mt = mkModes [modeName]
  res <- case rewriteOnce (mkTypeTheory mt) [rule] host of
    Left err -> assertFailure (T.unpack err)
    Right r -> pure r
  case res of
    Nothing -> assertFailure "expected rewrite inside box"
    Just d -> do
      let edges = IM.elems (dEdges d)
      case edges of
        [edge] ->
          case ePayload edge of
            PBox _ inner -> do
              got <- require (renderDiagram inner)
              expected <- require (renderDiagram g)
              got @?= expected
            _ -> assertFailure "expected box edge"
        _ -> assertFailure "expected single box edge"

testBoxMismatchRejects :: Assertion
testBoxMismatchRejects = do
  f <- require (mkGen "f" [aTy] [aTy])
  g <- require (mkGen "g" [aTy] [aTy])
  lhs <- require (mkBoxDiagram "B" f aTy)
  rhs <- require (mkBoxDiagram "B" g aTy)
  let rule = RewriteRule
        { rrName = "box-mismatch"
        , rrLHS = lhs
        , rrRHS = rhs
        , rrTyVars = []
        , rrIxVars = []
        }
  host <- require (mkBoxDiagram "B" g aTy)
  let mt = mkModes [modeName]
  res <- case rewriteOnce (mkTypeTheory mt) [rule] host of
    Left err -> assertFailure (T.unpack err)
    Right r -> pure r
  case res of
    Nothing -> pure ()
    Just _ -> assertFailure "expected box mismatch to reject"

testBoxMatchAccepts :: Assertion
testBoxMatchAccepts = do
  f1 <- require (mkGen "f" [aTy] [aTy])
  f2 <- require (mkGen "f" [aTy] [aTy])
  g <- require (mkGen "g" [aTy] [aTy])
  lhs <- require (mkBoxDiagram "B" f1 aTy)
  rhs <- require (mkBoxDiagram "B" g aTy)
  let rule = RewriteRule
        { rrName = "box-match"
        , rrLHS = lhs
        , rrRHS = rhs
        , rrTyVars = []
        , rrIxVars = []
        }
  host <- require (mkBoxDiagram "B" f2 aTy)
  let mt = mkModes [modeName]
  res <- case rewriteOnce (mkTypeTheory mt) [rule] host of
    Left err -> assertFailure (T.unpack err)
    Right r -> pure r
  case res of
    Nothing -> assertFailure "expected box match to succeed"
    Just d -> do
      let edges = IM.elems (dEdges d)
      case edges of
        [edge] ->
          case ePayload edge of
            PBox _ inner -> do
              got <- require (renderDiagram inner)
              expected <- require (renderDiagram g)
              got @?= expected
            _ -> assertFailure "expected box edge"
        _ -> assertFailure "expected single box edge"

testNestedBoxesMatch :: Assertion
testNestedBoxesMatch = do
  f <- require (mkGen "f" [aTy] [aTy])
  inner <- require (mkBoxDiagram "Inner" f aTy)
  lhs <- require (mkBoxDiagram "Outer" inner aTy)
  host <- require (mkBoxDiagram "Outer" inner aTy)
  res <- case findFirstMatchNoDoc lhs host of
    Left err -> assertFailure (T.unpack err)
    Right m -> pure m
  case res of
    Nothing -> assertFailure "expected nested box match"
    Just _ -> pure ()

testBoxTypeVarUnify :: Assertion
testBoxTypeVarUnify = do
  let aVar = tvar "a"
  let aVarTy = TVar aVar
  let aName = TypeName "A"
  let aConcrete = TCon (TypeRef modeName aName) []
  fVar <- require (mkGen "f" [aVarTy] [aVarTy])
  fConcrete <- require (mkGen "f" [aConcrete] [aConcrete])
  lhs <- require (mkBoxDiagram "B" fVar aVarTy)
  host <- require (mkBoxDiagram "B" fConcrete aConcrete)
  res <- case findFirstMatchWithTyVarsNoDoc (S.singleton aVar) lhs host of
    Left err -> assertFailure (T.unpack err)
    Right m -> pure m
  case res of
    Nothing -> assertFailure "expected type-var unification through box"
    Just m ->
      case M.lookup aVar (sTy (mTySubst m)) of
        Nothing -> assertFailure "expected substitution for type variable"
        Just ty -> ty @?= aConcrete

testRewriteUsesModeEq :: Assertion
testRewriteUsesModeEq = do
  let modeA = ModeName "A"
  let modeB = ModeName "B"
  let fName = ModName "F"
  let uName = ModName "U"
  mt0 <- require (addMode modeA (mkModes []))
  mt1 <- require (addMode modeB mt0)
  mt2 <- require (addModDecl (ModDecl { mdName = fName, mdSrc = modeA, mdTgt = modeB }) mt1)
  mt3 <- require (addModDecl (ModDecl { mdName = uName, mdSrc = modeB, mdTgt = modeA }) mt2)
  let lhsEq = ModExpr { meSrc = modeA, meTgt = modeA, mePath = [fName, uName] }
  let rhsEq = ModExpr { meSrc = modeA, meTgt = modeA, mePath = [] }
  mt <- require (addModEqn (ModEqn lhsEq rhsEq) mt3)
  let base = TCon (TypeRef modeA (TypeName "Base")) []
  let fExpr = ModExpr { meSrc = modeA, meTgt = modeB, mePath = [fName] }
  let uExpr = ModExpr { meSrc = modeB, meTgt = modeA, mePath = [uName] }
  let ufBase = TMod uExpr (TMod fExpr base)
  lhs <- require (genD modeA [base] [base] (GenName "foo"))
  let rhs = idD modeA [base]
  host <- require (genD modeA [ufBase] [ufBase] (GenName "foo"))
  let rule = RewriteRule { rrName = "foo_id", rrLHS = lhs, rrRHS = rhs, rrTyVars = [], rrIxVars = [] }
  res <- require (rewriteOnce (mkTypeTheory mt) [rule] host)
  out <-
    case res of
      Nothing -> assertFailure "expected rewrite to fire" >> fail "unreachable"
      Just d -> pure d
  let expected = idD modeA [base]
  iso <- require (diagramIsoEq out expected)
  assertBool "expected rewritten diagram to normalize to id[A.Base]" iso

testNormalizeDeterminism :: Assertion
testNormalizeDeterminism = do
  rule <- either (assertFailure . T.unpack) pure assocRule
  mul <- require (mkGen "mul" [aTy, aTy] [aTy])
  id1 <- pure (idD modeName [aTy])
  d1 <- require (tensorD mul id1)
  d2 <- require (compD (mkModes [modeName]) mul d1)
  let rules = [rule]
  let mt = mkModes [modeName]
  r1 <- require (normalize (mkTypeTheory mt) 10 rules d2)
  r2 <- require (normalize (mkTypeTheory mt) 10 rules d2)
  case (r1, r2) of
    (Finished a, Finished b) -> a @?= b
    (OutOfFuel a, OutOfFuel b) -> a @?= b
    _ -> assertFailure "expected same normalization status"

mkBoxDiagram :: Text -> Diagram -> TypeExpr -> Either Text Diagram
mkBoxDiagram name inner ty = do
  let (inP, d0) = freshPort ty (emptyDiagram modeName [])
  let (outP, d1) = freshPort ty d0
  let boxEdge = PBox (BoxName name) inner
  d2 <- addEdgePayload boxEdge [inP] [outP] d1
  pure d2 { dIn = [inP], dOut = [outP] }
