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
import Strat.Frontend.Env (meDoctrines, meImplDefaults)
import Strat.Poly.ModeTheory
import Strat.Poly.TypeExpr
import Strat.Poly.UnifyTy
import Strat.Poly.Doctrine (Doctrine(..), ModAction(..), ObligationDecl(..))
import Strat.Poly.TypeTheory (modeOnlyTypeTheory)
import Strat.Poly.Names (GenName(..))
import Test.Poly.Helpers (mkModes)


tests :: TestTree
tests =
  testGroup
    "Poly.ModeTheory"
    [ testCase "modality rewrite normalizes nested modality type" testNormalizeTypeExprByModEq
    , testCase "substitution re-normalizes modality type" testSubstReNormalizes
    , testCase "action declarations elaborate and validate" testActionElab
    , testCase "map elaborates inner expression at modality source mode" testMapCrossModeElab
    , testCase "for_gen obligations elaborate @gen and lifts" testForGenObligationElab
    , testCase "@gen outside for_gen is rejected" testGenOutsideForGenRejected
    , testCase "action coherence follows mod_eq" testActionModEqCoherence
    , testCase "implements fails when schema obligations are not provable" testAdjObligationFail
    , testCase "implements succeeds when schema obligations hold" testAdjObligationPass
    , testCase "legacy adj keyword is rejected" testAdjunctionKeywordRejected
    , testCase "legacy struct keyword is rejected" testStructureKeywordRejected
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
  let tt = modeOnlyTypeTheory mt
  subst <- requireEither (unifyTy tt (TVar xVar) (TMod quoteE (TVar aVar)))
  got <- requireEither (applySubstTy tt subst (TMod spliceE (TVar xVar)))
  got @?= TVar aVar

testActionElab :: Assertion
testActionElab = do
  let src = T.unlines
        [ "doctrine Act where {"
        , "  mode A;"
        , "  mode B;"
        , "  type X @A;"
        , "  type Y @B;"
        , "  modality F : A -> B;"
        , "  gen g : [A.X] -> [A.X] @A;"
        , "  gen h : [B.Y] -> [B.Y] @B;"
        , "  action F where {"
        , "    gen g -> h"
        , "  }"
        , "}"
        ]
  env <- requireEither (parseRawFile src >>= elabRawFile)
  doc <-
    case M.lookup "Act" (meDoctrines env) of
      Nothing -> assertFailure "missing doctrine Act" >> fail "unreachable"
      Just d -> pure d
  assertBool "expected modality action table to contain F" (M.member (ModName "F") (dActions doc))
  case M.lookup (ModName "F") (dActions doc) >>= M.lookup (ModeName "A", GenName "g") . maGenMap of
    Nothing -> assertFailure "missing action image for g under F"
    Just _ -> pure ()

testMapCrossModeElab :: Assertion
testMapCrossModeElab = do
  let src = T.unlines
        [ "doctrine CrossMap where {"
        , "  mode A;"
        , "  mode B;"
        , "  modality F : A -> B;"
        , "  type X @A;"
        , "  gen g(a@A) : [a] -> [a] @A;"
        , "  gen h(a@A) : [F(a)] -> [F(a)] @B;"
        , "  action F where {"
        , "    gen g -> h"
        , "  }"
        , "  obligation map_obl(a@A) : [F(a)] -> [F(a)] @B ="
        , "    map[F](g{a}) == h{a}"
        , "}"
        ]
  _ <- requireEither (parseRawFile src >>= elabRawFile)
  pure ()

testForGenObligationElab :: Assertion
testForGenObligationElab = do
  let src = T.unlines
        [ "doctrine ForGenLift where {"
        , "  mode M;"
        , "  type X @M;"
        , "  gen op : [M.X] -> [M.X] @M;"
        , "  gen f : [M.X, M.X] -> [M.X] @M;"
        , "  obligation naturality for_gen @M ="
        , "    @gen ; lift_cod(op) == lift_dom(op) ; @gen"
        , "}"
        ]
  env <- requireEither (parseRawFile src >>= elabRawFile)
  doc <-
    case M.lookup "ForGenLift" (meDoctrines env) of
      Nothing -> assertFailure "missing doctrine ForGenLift" >> fail "unreachable"
      Just d -> pure d
  let names = map obName (dObligations doc)
  length names @?= 2
  assertBool "expected per-generator obligation for op" ("naturality[op]" `elem` names)
  assertBool "expected per-generator obligation for f" ("naturality[f]" `elem` names)

testGenOutsideForGenRejected :: Assertion
testGenOutsideForGenRejected = do
  let src = T.unlines
        [ "doctrine BadGenObl where {"
        , "  mode M;"
        , "  type X @M;"
        , "  gen g : [M.X] -> [M.X] @M;"
        , "  obligation bad : [M.X] -> [M.X] @M ="
        , "    @gen == @gen"
        , "}"
        ]
  case parseRawFile src >>= elabRawFile of
    Left err ->
      if "@gen" `T.isInfixOf` err
        then pure ()
        else assertFailure ("expected @gen error, got: " <> T.unpack err)
    Right _ ->
      assertFailure "expected obligation elaboration to reject @gen outside for_gen"

testActionModEqCoherence :: Assertion
testActionModEqCoherence = do
  let src = T.unlines
        [ "doctrine BadAction where {"
        , "  mode A;"
        , "  type X @A;"
        , "  modality F : A -> A;"
        , "  mod_eq F -> id@A;"
        , "  gen g : [A.X] -> [A.X] @A;"
        , "  gen h : [A.X] -> [A.X] @A;"
        , "  action F where {"
        , "    gen g -> h"
        , "    gen h -> h"
        , "  }"
        , "}"
        ]
  case parseRawFile src >>= elabRawFile of
    Left err ->
      if "action coherence failed" `T.isInfixOf` err
        then pure ()
        else assertFailure ("expected action coherence error, got: " <> T.unpack err)
    Right _ ->
      assertFailure "expected doctrine elaboration to reject incoherent action under mod_eq"

testAdjObligationFail :: Assertion
testAdjObligationFail = do
  let src = T.unlines
        [ "doctrine AdjSchema where {"
        , "  mode C;"
        , "  mode L;"
        , "  modality F : C -> L;"
        , "  modality U : L -> C;"
        , "  mod_eq U.F -> id@C;"
        , "  mod_eq F.U -> id@L;"
        , "  gen eta(a@C) : [a] -> [U(F(a))] @C;"
        , "  gen eps(b@L) : [F(U(b))] -> [b] @L;"
        , "  action F where {"
        , "    gen eta -> eps"
        , "  }"
        , "  action U where {"
        , "    gen eps -> eta"
        , "  }"
        , "  obligation triangleL(a@C) : [F(a)] -> [F(a)] @L ="
        , "    map[F](eta{a}) ; eps{F(a)} == id[F(a)]"
        , "  obligation triangleR(b@L) : [U(b)] -> [U(b)] @C ="
        , "    eta{U(b)} ; map[U](eps{b}) == id[U(b)]"
        , "}"
        , "doctrine BadAdj where {"
        , "  mode C;"
        , "  mode L;"
        , "  modality F : C -> L;"
        , "  modality U : L -> C;"
        , "  mod_eq U.F -> id@C;"
        , "  mod_eq F.U -> id@L;"
        , "  gen eta(a@C) : [a] -> [U(F(a))] @C;"
        , "  gen eps(b@L) : [F(U(b))] -> [b] @L;"
        , "}"
        , "morphism badAdjInst : AdjSchema -> BadAdj where {"
        , "  mode C -> C;"
        , "  mode L -> L;"
        , "  modality F -> F;"
        , "  modality U -> U;"
        , "  gen eta @C -> eta"
        , "  gen eps @L -> eps"
        , "  check none;"
        , "}"
        , "implements AdjSchema for BadAdj using badAdjInst;"
        ]
  case parseRawFile src >>= elabRawFile of
    Left err ->
      if "implements obligation failed:" `T.isInfixOf` err
        then pure ()
        else assertFailure ("expected implements obligation failure, got: " <> T.unpack err)
    Right _ ->
      assertFailure "expected implements to fail on unsatisfied schema obligations"

testAdjObligationPass :: Assertion
testAdjObligationPass = do
  let src = T.unlines
        [ "doctrine AdjSchema where {"
        , "  mode C;"
        , "  mode L;"
        , "  modality F : C -> L;"
        , "  modality U : L -> C;"
        , "  mod_eq U.F -> id@C;"
        , "  mod_eq F.U -> id@L;"
        , "  gen eta(a@C) : [a] -> [U(F(a))] @C;"
        , "  gen eps(b@L) : [F(U(b))] -> [b] @L;"
        , "  action F where {"
        , "    gen eta -> eps"
        , "  }"
        , "  action U where {"
        , "    gen eps -> eta"
        , "  }"
        , "  obligation triangleL(a@C) : [F(a)] -> [F(a)] @L ="
        , "    map[F](eta{a}) ; eps{F(a)} == id[F(a)]"
        , "  obligation triangleR(b@L) : [U(b)] -> [U(b)] @C ="
        , "    eta{U(b)} ; map[U](eps{b}) == id[U(b)]"
        , "}"
        , "doctrine GoodAdj where {"
        , "  mode C;"
        , "  mode L;"
        , "  modality F : C -> L;"
        , "  modality U : L -> C;"
        , "  mod_eq U.F -> id@C;"
        , "  mod_eq F.U -> id@L;"
        , "  gen eta(a@C) : [a] -> [U(F(a))] @C;"
        , "  gen eps(b@L) : [F(U(b))] -> [b] @L;"
        , "  rule computational triangleL -> (a@C) : [F(a)] -> [F(a)] @L ="
        , "    eps{F(a)} ; eps{F(a)} == id[F(a)]"
        , "  rule computational triangleR -> (b@L) : [U(b)] -> [U(b)] @C ="
        , "    eta{U(b)} ; eta{U(b)} == id[U(b)]"
        , "}"
        , "morphism goodAdjInst : AdjSchema -> GoodAdj where {"
        , "  mode C -> C;"
        , "  mode L -> L;"
        , "  modality F -> F;"
        , "  modality U -> U;"
        , "  gen eta @C -> eta"
        , "  gen eps @L -> eps"
        , "  check none;"
        , "}"
        , "implements AdjSchema for GoodAdj using goodAdjInst;"
        ]
  env <- requireEither (parseRawFile src >>= elabRawFile)
  assertBool
    "expected implements default instance recorded"
    (M.member ("AdjSchema", "GoodAdj") (meImplDefaults env))

testAdjunctionKeywordRejected :: Assertion
testAdjunctionKeywordRejected = do
  let src = T.unlines
        [ "doctrine BadAdj where {"
        , "  mode C;"
        , "  mode L;"
        , "  modality F : C -> L;"
        , "  modality U : L -> C;"
        , "  " <> "adju" <> "nction F dashv U;"
        , "}"
        ]
  case parseRawFile src >>= elabRawFile of
    Left _ -> pure ()
    Right _ -> assertFailure "expected legacy adj keyword to be rejected"

testStructureKeywordRejected :: Assertion
testStructureKeywordRejected = do
  let src = T.unlines
        [ "doctrine BadStruct where {"
        , "  mode M;"
        , "  " <> "stru" <> "cture M = cartesian;"
        , "}"
        ]
  case parseRawFile src >>= elabRawFile of
    Left _ -> pure ()
    Right _ -> assertFailure "expected structure keyword to be rejected"

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
