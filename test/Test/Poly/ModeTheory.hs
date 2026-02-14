{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.ModeTheory
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Common.Rules (RewritePolicy(..))
import Strat.DSL.Parse (parseRawFile)
import Strat.DSL.Elab (elabRawFile)
import Strat.Frontend.Env (meDoctrines, meImplDefaults)
import Strat.Poly.ModeTheory
import Strat.Poly.TypeExpr
import Strat.Poly.UnifyTy
import Strat.Poly.Doctrine
  ( Doctrine(..)
  , ModAction(..)
  , ObligationDecl(..)
  , GenDecl(..)
  , InputShape(..)
  , TypeSig(..)
  , ParamSig(..)
  , doctrineTypeTheory
  )
import Strat.Poly.TypeTheory (modeOnlyTypeTheory)
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Diagram (genDTm, genD, diagramDom, diagramCod)
import Strat.Poly.Graph (Diagram(..))
import Strat.Poly.ModAction (applyAction)
import Strat.Poly.TermExpr (TermExpr(..), termExprToDiagram, diagramToTermExpr)
import Test.Poly.Helpers (mkModes)


tests :: TestTree
tests =
  testGroup
    "Poly.ModeTheory"
    [ testCase "modality rewrite normalizes nested modality type" testNormalizeTypeExprByModEq
    , testCase "substitution re-normalizes modality type" testSubstReNormalizes
    , testCase "action declarations elaborate and validate" testActionElab
    , testCase "applyAction preserves non-source tmctx and unifies using diagram tmctx" testApplyActionUsesDiagramTmCtx
    , testCase "applyAction weakens image term-context prefixes before splice" testApplyActionWeakenImageTmCtx
    , testCase "map elaborates inner expression at modality source mode" testMapCrossModeElab
    , testCase "for_gen obligations elaborate @gen and lifts" testForGenObligationElab
    , testCase "for_gen obligations expand over target generators during implements" testForGenImplementsQuantifiesTarget
    , testCase "@gen outside for_gen is rejected" testGenOutsideForGenRejected
    , testCase "action coherence follows mod_eq" testActionModEqCoherence
    , testCase "implements fails when schema obligations are not provable" testAdjObligationFail
    , testCase "implements succeeds when schema obligations hold" testAdjObligationPass
    , testCase "implements monad schema with map[T] laws against target action" testMonadObligationPass
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

testApplyActionUsesDiagramTmCtx :: Assertion
testApplyActionUsesDiagramTmCtx = do
  let modeC = ModeName "C"
  let modeI = ModeName "I"
  let modF = ModName "F"
  let natRef = TypeRef modeI (TypeName "Nat")
  let vecRef = TypeRef modeC (TypeName "Vec")
  let natTy = TCon natRef []
  let tmCtx = [natTy]
  mt0 <- requireEither (addMode modeC (mkModes []))
  mt1 <- requireEither (addMode modeI mt0)
  mt2 <- requireEither (addModDecl (ModDecl modF modeC modeC) mt1)
  let lhsEq = ModExpr { meSrc = modeC, meTgt = modeC, mePath = [modF] }
  let rhsEq = ModExpr { meSrc = modeC, meTgt = modeC, mePath = [] }
  mt <- requireEither (addModEqn (ModEqn lhsEq rhsEq) mt2)
  let tt0 = modeOnlyTypeTheory mt
  let tmParam = TmVar { tmvName = "n", tmvSort = natTy, tmvScope = 1 }
  tmParamTerm <- requireEither (termExprToDiagram tt0 tmCtx natTy (TMVar tmParam))
  tmBound0 <- requireEither (termExprToDiagram tt0 tmCtx natTy (TMBound 0))
  let vecParam = TCon vecRef [TATm tmParamTerm]
  let vecBound = TCon vecRef [TATm tmBound0]
  let genName = GenName "g"
  let genDecl =
        GenDecl
          { gdName = genName
          , gdMode = modeC
          , gdTyVars = []
          , gdTmVars = [tmParam]
          , gdDom = [InPort vecParam]
          , gdCod = [vecParam]
          , gdAttrs = []
          }
  image <- requireEither (genDTm modeC tmCtx [vecParam] [vecParam] genName)
  let doc =
        Doctrine
          { dName = "ActTmCtx"
          , dModes = mt
          , dAcyclicModes = S.empty
          , dAttrSorts = M.empty
          , dTypes =
              M.fromList
                [ (modeI, M.fromList [(TypeName "Nat", TypeSig [])])
                , (modeC, M.fromList [(TypeName "Vec", TypeSig [PS_Tm natTy])])
                ]
          , dGens = M.fromList [(modeC, M.fromList [(genName, genDecl)])]
          , dCells2 = []
          , dActions =
              M.fromList
                [ (modF, ModAction { maMod = modF, maGenMap = M.fromList [((modeC, genName), image)], maPolicy = UseOnlyComputationalLR, maFuel = 50 })
                ]
          , dObligations = []
          }
  let tt = doctrineTypeTheory doc
  srcDiag <- requireEither (genDTm modeC tmCtx [vecBound] [vecBound] genName)
  mapped <- requireEither (applyAction doc modF srcDiag)
  dTmCtx mapped @?= tmCtx
  dom <- requireEither (diagramDom mapped)
  cod <- requireEither (diagramCod mapped)
  dom @?= [vecBound]
  cod @?= [vecBound]
  case dom of
    [TCon _ [TATm tmOut]] -> do
      expr <- requireEither (diagramToTermExpr tt tmCtx natTy tmOut)
      expr @?= TMBound 0
    _ -> assertFailure "unexpected mapped boundary shape"

testApplyActionWeakenImageTmCtx :: Assertion
testApplyActionWeakenImageTmCtx = do
  let modeM = ModeName "M"
  let modF = ModName "F"
  let tyX = TCon (TypeRef modeM (TypeName "X")) []
  mt0 <- requireEither (addMode modeM (mkModes []))
  mt1 <- requireEither (addModDecl (ModDecl modF modeM modeM) mt0)
  let lhsEq = ModExpr { meSrc = modeM, meTgt = modeM, mePath = [modF] }
  let rhsEq = ModExpr { meSrc = modeM, meTgt = modeM, mePath = [] }
  mt <- requireEither (addModEqn (ModEqn lhsEq rhsEq) mt1)
  let genG = GenName "g"
  let genH = GenName "h"
  let mkGen name =
        GenDecl
          { gdName = name
          , gdMode = modeM
          , gdTyVars = []
          , gdTmVars = []
          , gdDom = [InPort tyX]
          , gdCod = [tyX]
          , gdAttrs = []
          }
  img <- requireEither (genD modeM [tyX] [tyX] genH)
  let doc =
        Doctrine
          { dName = "ActWeaken"
          , dModes = mt
          , dAcyclicModes = S.empty
          , dAttrSorts = M.empty
          , dTypes = M.singleton modeM (M.singleton (TypeName "X") (TypeSig []))
          , dGens = M.singleton modeM (M.fromList [(genG, mkGen genG), (genH, mkGen genH)])
          , dCells2 = []
          , dActions =
              M.singleton
                modF
                ModAction
                  { maMod = modF
                  , maGenMap = M.singleton (modeM, genG) img
                  , maPolicy = UseOnlyComputationalLR
                  , maFuel = 50
                  }
          , dObligations = []
          }
  srcDiag <- requireEither (genDTm modeM [tyX] [tyX] [tyX] genG)
  mapped <- requireEither (applyAction doc modF srcDiag)
  dTmCtx mapped @?= [tyX]

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
  let obls = dObligations doc
  length obls @?= 1
  case obls of
    [obl] -> do
      obName obl @?= "naturality"
      assertBool "expected for_gen template obligation" (obForGen obl)
    _ -> assertFailure "expected exactly one obligation template"

testForGenImplementsQuantifiesTarget :: Assertion
testForGenImplementsQuantifiesTarget = do
  let src = T.unlines
        [ "doctrine FGSchema where {"
        , "  mode M;"
        , "  type X @M;"
        , "  gen keep : [M.X] -> [M.X] @M;"
        , "  obligation all_id for_gen @M ="
        , "    @gen == id[M.X]"
        , "}"
        , "doctrine FGTgt where {"
        , "  mode M;"
        , "  type X @M;"
        , "  gen keep : [M.X] -> [M.X] @M;"
        , "  gen bad : [M.X] -> [M.X] @M;"
        , "  rule computational keep_id -> : [M.X] -> [M.X] @M ="
        , "    keep == id[M.X]"
        , "}"
        , "morphism fgInst : FGSchema -> FGTgt where {"
        , "  mode M -> M;"
        , "  gen keep @M -> keep"
        , "  check none;"
        , "}"
        , "implements FGSchema for FGTgt using fgInst;"
        ]
  case parseRawFile src >>= elabRawFile of
    Left err ->
      if "implements obligation failed: all_id[bad]" `T.isInfixOf` err
        then pure ()
        else assertFailure ("expected for_gen target quantification failure, got: " <> T.unpack err)
    Right _ ->
      assertFailure "expected implements to fail on unsatisfied for_gen obligation for target generator"

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
        , "  action F where {"
        , "    gen eta -> eps"
        , "  }"
        , "  action U where {"
        , "    gen eps -> eta"
        , "  }"
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
        , "  action F where {"
        , "    gen eta -> eps"
        , "  }"
        , "  action U where {"
        , "    gen eps -> eta"
        , "  }"
        , "  rule computational eta_id -> (a@C) : [a] -> [a] @C ="
        , "    eta{a} ; eta{a} == id[a]"
        , "  rule computational eps_id -> (b@L) : [b] -> [b] @L ="
        , "    eps{b} ; eps{b} == id[b]"
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

testMonadObligationPass :: Assertion
testMonadObligationPass = do
  let src = T.unlines
        [ "doctrine SchemaMonad where {"
        , "  mode C;"
        , "  modality T : C -> C;"
        , "  gen ret(x@C) : [x] -> [T(x)] @C;"
        , "  gen join(x@C) : [T(T(x))] -> [T(x)] @C;"
        , "  obligation leftUnit(a@C) : [T(a)] -> [T(a)] @C ="
        , "    map[T](ret{a}) ; join{a} == id[T(a)]"
        , "  obligation rightUnit(a@C) : [T(a)] -> [T(a)] @C ="
        , "    ret{T(a)} ; join{a} == id[T(a)]"
        , "  obligation assoc(a@C) : [T(T(T(a)))] -> [T(a)] @C ="
        , "    map[T](join{a}) ; join{a} == join{T(a)} ; join{a}"
        , "}"
        , "doctrine IdMonad where {"
        , "  mode C;"
        , "  modality T : C -> C;"
        , "  type A @C;"
        , "  gen ret(a@C) : [a] -> [T(a)] @C;"
        , "  gen join(a@C) : [T(T(a))] -> [T(a)] @C;"
        , "  action T where {"
        , "    gen ret -> ret"
        , "    gen join -> join"
        , "  }"
        , "  rule computational unit -> (a@C) : [T(a)] -> [T(a)] @C ="
        , "    ret{T(a)} ; join{a} == id[T(a)]"
        , "}"
        , "morphism monadInst : SchemaMonad -> IdMonad where {"
        , "  mode C -> C;"
        , "  modality T -> T;"
        , "  gen ret @C -> ret"
        , "  gen join @C -> join"
        , "  check none;"
        , "}"
        , "implements SchemaMonad for IdMonad using monadInst;"
        ]
  env <- requireEither (parseRawFile src >>= elabRawFile)
  assertBool
    "expected monad implements default instance recorded"
    (M.member ("SchemaMonad", "IdMonad") (meImplDefaults env))

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
