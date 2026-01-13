{-# LANGUAGE OverloadedStrings #-}
module Test.Kernel.DoctrineExpr
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.Kernel.DoctrineExpr
import Strat.Kernel.Presentation
import Strat.Kernel.Rewrite
import Strat.Kernel.RewriteSystem
import Strat.Kernel.Rule
import Strat.Kernel.Signature
import Strat.Kernel.Syntax
import Strat.Kernel.Term
import Strat.Kernel.Types
import qualified Data.Map.Strict as M
import Data.Text (Text)
import Test.Kernel.Fixtures

tests :: TestTree
tests =
  testGroup
    "Kernel.DoctrineExpr"
    [ testCase "disjoint qualifies" testDisjointQualifies
    , testCase "disjoint no cross-apply" testDisjointNoCross
    , testCase "share ops enables cross-apply" testShareOps
    , testCase "share ops with mismatch fails" testShareOpsMismatch
    , testCase "share sorts with mismatch fails" testShareSortsMismatch
    , testCase "rename eqs resolves collisions" testRenameEqs
    , testCase "rename ops updates terms" testRenameOps
    , testCase "share unknown op fails" testShareUnknown
    ]

mkUnaryEq :: Text -> Text -> Text -> Equation
mkUnaryEq name lhsOp rhsOp =
  let scope = ScopeId ("eq:" <> name)
      vx = Var scope 0
      x = mkVar objSort vx
  in Equation
      { eqName = name
      , eqClass = Computational
      , eqOrient = LR
      , eqTele = [Binder vx objSort]
      , eqLHS = mkTerm sigBasic lhsOp [x]
      , eqRHS = mkTerm sigBasic rhsOp [x]
      }

presA :: Presentation
presA =
  Presentation
    { presName = "A"
    , presSig = sigBasic
    , presEqs = [mkUnaryEq "r" "f" "g"]
    }

presB :: Presentation
presB =
  Presentation
    { presName = "B"
    , presSig = sigBasic
    , presEqs = [mkUnaryEq "r" "f" "h"]
    }

termRootOp :: Term -> Maybe OpName
termRootOp tm =
  case termNode tm of
    TOp op _ -> Just op
    _ -> Nothing

mkTermQ :: Signature -> Text -> [Term] -> Term
mkTermQ sig name args = mkTerm sig name args

testDisjointQualifies :: Assertion
testDisjointQualifies = do
  let expr = And (Atom "A" presA) (Atom "B" presB)
  case elabDocExpr expr of
    Left err -> assertFailure (show err)
    Right pres -> do
      map eqName (presEqs pres) @?= ["A.r", "B.r"]
      case presEqs pres of
        (e1 : e2 : _) -> do
          termRootOp (eqLHS e1) @?= Just (OpName "A.f")
          termRootOp (eqLHS e2) @?= Just (OpName "B.f")
        _ -> assertFailure "expected two equations"

testDisjointNoCross :: Assertion
testDisjointNoCross = do
  let expr = And (Atom "A" presA) (Atom "B" presB)
  case (elabDocExpr expr, compileDocExpr UseOnlyComputationalLR expr) of
    (Right pres, Right rs) -> do
      let sig = presSig pres
      let t = mkTermQ sig "A.f" [mkTermQ sig "A.a" []]
      let reds = rewriteOnce rs t
      map (stepRule . redexStep) reds @?= [RuleId "A.r" DirLR]
    (Left err, _) -> assertFailure (show err)
    (_, Left err) -> assertFailure (show err)

testShareOps :: Assertion
testShareOps = do
  let base = And (Atom "A" presA) (Atom "B" presB)
  let expr =
        ShareOps
          [(OpName "A.f", OpName "B.f")]
          (ShareSorts [(SortName "A.Obj", SortName "B.Obj")] base)
  case (elabDocExpr expr, compileDocExpr UseOnlyComputationalLR expr) of
    (Right pres, Right rs) -> do
      let sig = presSig pres
      let t = mkTermQ sig "A.f" [mkTermQ sig "A.a" []]
      let reds = rewriteOnce rs t
      map (stepRule . redexStep) reds
        @?= [RuleId "A.r" DirLR, RuleId "B.r" DirLR]
    (Left err, _) -> assertFailure (show err)
    (_, Left err) -> assertFailure (show err)

testShareOpsMismatch :: Assertion
testShareOpsMismatch = do
  let badSig =
        sigBasic
          { sigOps = M.insert opF (OpDecl opF [Binder (Var (ScopeId "op:f") 0) objSort, Binder (Var (ScopeId "op:f") 1) objSort] objSort) (sigOps sigBasic)
          }
  let presBad = presA { presSig = badSig }
  let expr = ShareOps [(OpName "A.f", OpName "B.f")] (And (Atom "A" presBad) (Atom "B" presB))
  case elabDocExpr expr of
    Left _ -> pure ()
    Right _ -> assertFailure "expected share ops mismatch"

testShareSortsMismatch :: Assertion
testShareSortsMismatch = do
  let badSig =
        sigBasic
          { sigSortCtors = M.insert objName (SortCtor objName [objSort]) (sigSortCtors sigBasic)
          }
  let presBad = presA { presSig = badSig }
  let expr = ShareSorts [(SortName "A.Obj", SortName "B.Obj")] (And (Atom "A" presBad) (Atom "B" presB))
  case elabDocExpr expr of
    Left _ -> pure ()
    Right _ -> assertFailure "expected share sorts mismatch"

testRenameEqs :: Assertion
testRenameEqs = do
  let expr =
        And
          (Atom "C" presA)
          (RenameEqs (M.fromList [("C.r", "C.r2")]) (Atom "C" presB))
  case elabDocExpr expr of
    Left err -> assertFailure (show err)
    Right pres -> map eqName (presEqs pres) @?= ["C.r", "C.r2"]

testRenameOps :: Assertion
testRenameOps = do
  let expr = RenameOps (M.fromList [(OpName "A.g", OpName "A.g2")]) (Atom "A" presA)
  case elabDocExpr expr of
    Left err -> assertFailure (show err)
    Right pres ->
      case presEqs pres of
        (e1 : _) -> termRootOp (eqRHS e1) @?= Just (OpName "A.g2")
        _ -> assertFailure "expected equation"

testShareUnknown :: Assertion
testShareUnknown = do
  let expr = ShareOps [(OpName "A.missing", OpName "B.f")] (And (Atom "A" presA) (Atom "B" presB))
  case elabDocExpr expr of
    Left _ -> pure ()
    Right _ -> assertFailure "expected unknown op error"
