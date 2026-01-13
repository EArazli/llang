{-# LANGUAGE OverloadedStrings #-}
module Test.Kernel.CriticalPairs
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.Kernel.CriticalPairs
import Strat.Kernel.Presentation
import Strat.Kernel.RewriteSystem
import Strat.Kernel.Rule
import Strat.Kernel.Syntax
import Strat.Kernel.Term
import Strat.Kernel.Types
import Strat.Kernel.Subst
import Strat.Kernel.Unify
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import Test.Kernel.Fixtures

tests :: TestTree
tests =
  testGroup
    "Kernel.CriticalPairs"
    [ testCase "root overlap included" testRootOverlap
    , testCase "variable overlap included" testVarOverlap
    , testCase "inner variable overlap included" testInnerVarOverlap
    , testCase "self-overlap freshens scopes" testSelfOverlapFreshening
    , testCase "CPMode filtering" testCPModeFiltering
    , testCase "critical pair soundness" testSoundness
    , testCase "non-left-linear rule allowed" testNonLinearAllowed
    , testCase "criticalPairsBounded subset" testBoundedSubset
    , testCase "criticalPairsForRules respects allowed set" testForRulesSubset
    ]

mkEqUnary :: Text -> Text -> Text -> RuleClass -> Equation
mkEqUnary name lhsOp rhsOp cls =
  let scope = ScopeId ("eq:" <> name)
      vx = Var scope 0
      x = mkVar objSort vx
  in Equation
      { eqName = name
      , eqClass = cls
      , eqOrient = LR
      , eqTele = [Binder vx objSort]
      , eqLHS = mkTerm sigBasic lhsOp [x]
      , eqRHS = mkTerm sigBasic rhsOp [x]
      }

mkEqConst :: Text -> Text -> Text -> RuleClass -> Equation
mkEqConst name l r cls =
  Equation
    { eqName = name
    , eqClass = cls
    , eqOrient = LR
    , eqTele = []
    , eqLHS = mkTerm sigBasic l []
    , eqRHS = mkTerm sigBasic r []
    }

mkEqNested :: Text -> Equation
mkEqNested name =
  let scope = ScopeId ("eq:" <> name)
      vx = Var scope 0
      x = mkVar objSort vx
      lhsTerm = mkTerm sigBasic "h" [mkTerm sigBasic "f" [x]]
      rhsTerm = mkTerm sigBasic "k" [x]
  in Equation
      { eqName = name
      , eqClass = Computational
      , eqOrient = LR
      , eqTele = [Binder vx objSort]
      , eqLHS = lhsTerm
      , eqRHS = rhsTerm
      }

mkRS :: [Equation] -> RewriteSystem
mkRS eqs =
  case compileRewriteSystem UseAllOriented (Presentation "P" sigBasic eqs) of
    Left err -> error (show err)
    Right rs -> rs

testRootOverlap :: Assertion
testRootOverlap = do
  let eq1 = mkEqUnary "r1" "f" "g" Computational
  let eq2 = mkEqUnary "r2" "f" "h" Computational
  let rs = mkRS [eq1, eq2]
  case criticalPairs CP_All rs of
    Left err -> assertFailure (show err)
    Right cps -> assertBool "expected root overlap" (any ((== []) . cpPosIn2) cps)

testVarOverlap :: Assertion
testVarOverlap = do
  let scope = ScopeId "eq:r2"
  let vx = Var scope 0
  let x = mkVar objSort vx
  let eq1 = mkEqUnary "r1" "f" "g" Computational
  let eq2 =
        Equation
          { eqName = "r2"
          , eqClass = Computational
          , eqOrient = LR
          , eqTele = [Binder vx objSort]
          , eqLHS = x
          , eqRHS = mkTerm sigBasic "h" [x]
          }
  let rs = mkRS [eq1, eq2]
  case criticalPairs CP_All rs of
    Left err -> assertFailure (show err)
    Right cps ->
      assertBool
        "expected overlap into variable lhs"
        (any (\cp -> cpRule2 cp == RuleId "r2" DirLR && cpPosIn2 cp == []) cps)

testInnerVarOverlap :: Assertion
testInnerVarOverlap = do
  let scope = ScopeId "eq:dup"
  let vx = Var scope 0
  let x = mkVar objSort vx
  let eq1 = mkEqConst "r1" "a" "b" Computational
  let eq2 =
        Equation
          { eqName = "dup"
          , eqClass = Computational
          , eqOrient = LR
          , eqTele = [Binder vx objSort]
          , eqLHS = mkTerm sigBasic "m" [x, x]
          , eqRHS = mkTerm sigBasic "f" [x]
          }
  let rs = mkRS [eq1, eq2]
  case criticalPairs CP_All rs of
    Left err -> assertFailure (show err)
    Right cps ->
      assertBool
        "expected inner variable overlap"
        (any (\cp -> cpRule1 cp == RuleId "r1" DirLR && cpRule2 cp == RuleId "dup" DirLR && cpPosIn2 cp == [0]) cps)

testSelfOverlapFreshening :: Assertion
testSelfOverlapFreshening = do
  let eq1 = mkEqUnary "r1" "f" "g" Computational
  let rs = mkRS [eq1]
  case criticalPairs CP_All rs of
    Left err -> assertFailure (show err)
    Right cps -> do
      let scopes =
            case filter (\cp -> cpRule1 cp == RuleId "r1" DirLR && cpRule2 cp == RuleId "r1" DirLR) cps of
              [] -> S.empty
              (cp : _) -> scopesInSubst (cpMgu cp)
      let has0 = any (T.isPrefixOf "cp:r1:0:") (map renderScope (S.toList scopes))
      let has1 = any (T.isPrefixOf "cp:r1:1:") (map renderScope (S.toList scopes))
      assertBool "expected scopes from both sides" (has0 && has1)
  where
    renderScope (ScopeId t) = t

testCPModeFiltering :: Assertion
testCPModeFiltering = do
  let eqS = mkEqUnary "s" "f" "g" Structural
  let eqC = mkEqUnary "c" "f" "h" Computational
  let rs = mkRS [eqS, eqC]
  case criticalPairs CP_OnlyStructural rs of
    Left err -> assertFailure (show err)
    Right cps ->
      assertBool
        "expected only structural pairs"
        (all (\cp -> cpRule1 cp == RuleId "s" DirLR && cpRule2 cp == RuleId "s" DirLR) cps)
  case criticalPairs CP_StructuralVsComputational rs of
    Left err -> assertFailure (show err)
    Right cps ->
      assertBool
        "expected mixed pairs"
        (all (\cp -> cpRule1 cp /= cpRule2 cp) cps)

testSoundness :: Assertion
testSoundness = do
  let eq1 = mkEqUnary "r1" "f" "g" Computational
  let eq2 = mkEqNested "r2"
  let rs = mkRS [eq1, eq2]
  case criticalPairs CP_All rs of
    Left err -> assertFailure (show err)
    Right cps ->
      case filter (\cp -> cpRule1 cp == RuleId "r1" DirLR && cpRule2 cp == RuleId "r2" DirLR) cps of
        [] -> assertFailure "expected critical pair"
        (cp : _) -> do
          let r1 = getRule rs (RuleId "r1" DirLR)
          let r2 = getRule rs (RuleId "r2" DirLR)
          let r1' = renameRule "0" r1
          let r2' = renameRule "1" r2
          let sub = case subtermAt (lhs r2') (cpPosIn2 cp) of
                      Nothing -> error "missing subterm"
                      Just t -> t
          case unify (lhs r1') sub of
            Nothing -> assertFailure "expected mgu"
            Just mgu -> do
              let replaced = case replaceAtChecked sigBasic (lhs r2') (cpPosIn2 cp) (rhs r1') of
                                Nothing -> error "replace failed"
                                Just t -> t
              let peak = applySubstTerm mgu (lhs r2')
              let left = applySubstTerm mgu replaced
              let right = applySubstTerm mgu (rhs r2')
              cpPeak cp @?= peak
              cpLeft cp @?= left
              cpRight cp @?= right
  where
    renameRule tag r =
      let scopes = scopesInTerm (lhs r) `S.union` scopesInTerm (rhs r)
          mapping =
            M.fromList
              [ (old, ScopeId ("cp:" <> ridEq (ruleId r) <> ":" <> tag <> ":" <> renderScope old))
              | old <- S.toList scopes
              ]
      in r
          { lhs = renameScopesWith mapping (lhs r)
          , rhs = renameScopesWith mapping (rhs r)
          }

    renameScopesWith m tm =
      Term
        { termSort = renameSort m (termSort tm)
        , termNode =
            case termNode tm of
              TVar v -> TVar (renameVar m v)
              TOp op args -> TOp op (map (renameScopesWith m) args)
        }

    renameVar m v =
      case M.lookup (vScope v) m of
        Nothing -> v
        Just new -> v { vScope = new }

    renameSort m (Sort name idx) =
      Sort name (map (renameScopesWith m) idx)

    renderScope (ScopeId t) = t

testNonLinearAllowed :: Assertion
testNonLinearAllowed = do
  let scope = ScopeId "eq:dup"
  let vx = Var scope 0
  let x = mkVar objSort vx
  let eq1 =
        Equation
          { eqName = "dup"
          , eqClass = Computational
          , eqOrient = LR
          , eqTele = [Binder vx objSort]
          , eqLHS = mkTerm sigBasic "m" [x, x]
          , eqRHS = mkTerm sigBasic "f" [x]
          }
  let rs = mkRS [eq1]
  case criticalPairs CP_All rs of
    Left err -> assertFailure (show err)
    Right _ -> pure ()

testBoundedSubset :: Assertion
testBoundedSubset = do
  let eq1 = mkEqUnary "r1" "f" "g" Computational
  let eq2 = mkEqNested "r2"
  let rs = mkRS [eq1, eq2]
  case criticalPairs CP_All rs of
    Left err -> assertFailure (show err)
    Right cps ->
      case criticalPairsBounded 1 CP_All rs of
        Left err -> assertFailure (show err)
        Right bounded ->
          assertBool "bounded should be subset" (length bounded <= length cps)

testForRulesSubset :: Assertion
testForRulesSubset = do
  let eq1 = mkEqUnary "r1" "f" "g" Computational
  let scope = ScopeId "eq:dup"
  let vx = Var scope 0
  let x = mkVar objSort vx
  let eq2 =
        Equation
          { eqName = "dup"
          , eqClass = Computational
          , eqOrient = LR
          , eqTele = [Binder vx objSort]
          , eqLHS = mkTerm sigBasic "m" [x, x]
          , eqRHS = mkTerm sigBasic "f" [x]
          }
  let rs = mkRS [eq1, eq2]
  let allowed = S.singleton (RuleId "r1" DirLR)
  case criticalPairsForRules allowed CP_All rs of
    Left err -> assertFailure (show err)
    Right cps ->
      assertBool "expected only allowed rule ids"
        (all (\cp -> cpRule1 cp `S.member` allowed && cpRule2 cp `S.member` allowed) cps)

scopesInSubst :: Subst -> S.Set ScopeId
scopesInSubst subst =
  let vars = S.fromList (M.keys subst) `S.union` S.unions (map varsTerm (M.elems subst))
  in S.map vScope vars
