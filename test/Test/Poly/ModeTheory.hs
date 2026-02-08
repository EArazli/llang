{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.ModeTheory
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import Strat.DSL.Parse (parseRawFile)
import Strat.DSL.Elab (elabRawFile)
import Strat.Frontend.Env (meDoctrines)
import Strat.Poly.ModeTheory
import Strat.Poly.TypeExpr
import Strat.Poly.UnifyTy
import Strat.Poly.Doctrine (Doctrine(..), GenDecl(..))
import Strat.Poly.Names (GenName(..))
import Test.Poly.Helpers (mkModes)


tests :: TestTree
tests =
  testGroup
    "Poly.ModeTheory"
    [ testCase "modality rewrite normalizes nested modality type" testNormalizeTypeExprByModEq
    , testCase "substitution re-normalizes modality type" testSubstReNormalizes
    , testCase "adjunction auto-generates unit/counit generators" testAdjunctionGens
    , testCase "structural dup with attributes is rejected directly" testDupAttrsRejected
    ]

testNormalizeTypeExprByModEq :: Assertion
testNormalizeTypeExprByModEq = do
  mt <- requireEither (buildStagingTheory (ModeName "RT") (ModeName "CT"))
  let rt = ModeName "RT"
  let quote = ModName "quote"
  let splice = ModName "splice"
  let natRT = TCon (TypeRef rt (TypeName "Nat")) []
  let quoteE = ModExpr { meSrc = rt, meTgt = ModeName "CT", mePath = [quote] }
  let spliceE = ModExpr { meSrc = ModeName "CT", meTgt = rt, mePath = [splice] }
  got <- requireEither (normalizeTypeExpr mt (TMod spliceE (TMod quoteE natRT)))
  got @?= natRT

testSubstReNormalizes :: Assertion
testSubstReNormalizes = do
  mt <- requireEither (buildStagingTheory (ModeName "RT") (ModeName "CT"))
  let rt = ModeName "RT"
  let ct = ModeName "CT"
  let quote = ModName "quote"
  let splice = ModName "splice"
  let xVar = TyVar { tvName = "x", tvMode = ct }
  let aVar = TyVar { tvName = "A", tvMode = rt }
  let quoteE = ModExpr { meSrc = rt, meTgt = ct, mePath = [quote] }
  let spliceE = ModExpr { meSrc = ct, meTgt = rt, mePath = [splice] }
  subst <- requireEither (unifyTy mt (TVar xVar) (TMod quoteE (TVar aVar)))
  let got = applySubstTy mt subst (TMod spliceE (TVar xVar))
  got @?= TVar aVar

testAdjunctionGens :: Assertion
testAdjunctionGens = do
  let src = T.unlines
        [ "doctrine LNL where {"
        , "  mode C;"
        , "  mode L;"
        , "  modality F : C -> L;"
        , "  modality U : L -> C;"
        , "  adjunction F dashv U;"
        , "  type Nat @C;"
        , "  type Nat @L;"
        , "}"
        ]
  env <- requireEither (parseRawFile src >>= elabRawFile)
  doc <-
    case M.lookup "LNL" (meDoctrines env) of
      Nothing -> assertFailure "missing doctrine LNL" >> fail "unreachable"
      Just d -> pure d
  let modeC = ModeName "C"
  let modeL = ModeName "L"
  unitGen <-
    case M.lookup modeC (dGens doc) >>= M.lookup (GenName "unit_F") of
      Nothing -> assertFailure "missing unit_F in mode C" >> fail "unreachable"
      Just g -> pure g
  counitGen <-
    case M.lookup modeL (dGens doc) >>= M.lookup (GenName "counit_F") of
      Nothing -> assertFailure "missing counit_F in mode L" >> fail "unreachable"
      Just g -> pure g
  case gdTyVars unitGen of
    [a] -> do
      gdDom unitGen @?= [TVar a]
      let fExpr = ModExpr { meSrc = modeC, meTgt = modeL, mePath = [ModName "F"] }
      let uExpr = ModExpr { meSrc = modeL, meTgt = modeC, mePath = [ModName "U"] }
      cod <- requireEither (normalizeTypeExpr (dModes doc) (TMod uExpr (TMod fExpr (TVar a))))
      gdCod unitGen @?= [cod]
    _ -> assertFailure "unit_F should bind exactly one type variable"
  case gdTyVars counitGen of
    [b] -> do
      gdCod counitGen @?= [TVar b]
      let fExpr = ModExpr { meSrc = modeC, meTgt = modeL, mePath = [ModName "F"] }
      let uExpr = ModExpr { meSrc = modeL, meTgt = modeC, mePath = [ModName "U"] }
      dom <- requireEither (normalizeTypeExpr (dModes doc) (TMod fExpr (TMod uExpr (TVar b))))
      gdDom counitGen @?= [dom]
    _ -> assertFailure "counit_F should bind exactly one type variable"

testDupAttrsRejected :: Assertion
testDupAttrsRejected = do
  let src = T.unlines
        [ "doctrine BadStruct where {"
        , "  mode M;"
        , "  structure M = cartesian;"
        , "  attrsort Int = int;"
        , "  type A @M;"
        , "  gen dup (a@M) {n:Int} : [a] -> [a, a] @M;"
        , "  gen drop (a@M) : [a] -> [] @M;"
        , "}"
        ]
  case parseRawFile src >>= elabRawFile of
    Left err ->
      assertBool "expected direct dup-attrs structural error" ("must not declare attributes" `T.isInfixOf` err)
    Right _ -> assertFailure "expected doctrine validation failure"

buildStagingTheory :: ModeName -> ModeName -> Either T.Text ModeTheory
buildStagingTheory rt ct = do
  mt1 <- addMode rt (mkModes [])
  mt2 <- addMode ct mt1
  mt3 <- addModDecl (ModDecl { mdName = ModName "quote", mdSrc = rt, mdTgt = ct }) mt2
  mt4 <- addModDecl (ModDecl { mdName = ModName "splice", mdSrc = ct, mdTgt = rt }) mt3
  let lhs = ModExpr { meSrc = rt, meTgt = rt, mePath = [ModName "quote", ModName "splice"] }
  let rhs = ModExpr { meSrc = rt, meTgt = rt, mePath = [] }
  addModEqn (ModEqn lhs rhs) mt4

requireEither :: Either T.Text a -> IO a
requireEither =
  either (assertFailure . T.unpack) pure
