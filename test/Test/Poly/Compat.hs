{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.Compat
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Control.Monad (forM_)
import qualified Data.Map.Strict as M
import Strat.Kernel.Presentation (Presentation(..))
import Strat.Kernel.Rule (Equation(..))
import Strat.Kernel.Syntax (Binder(..), Var(..), ScopeId(..))
import Strat.Kernel.Term (mkVar)
import Strat.Kernel.Types (RuleClass(..), Orientation(..))
import Strat.Poly.Compat
import Strat.Poly.Cell2 (Cell2(..))
import Strat.Poly.Doctrine (Doctrine2(..), cartMode)
import Strat.Poly.Eval (diagramToTerm1)
import Test.Kernel.Fixtures


tests :: TestTree
tests =
  testGroup
    "Poly.Compat"
    [ testCase "term -> diagram -> term" testRoundtripTerms
    , testCase "presentation compiles to cells" testPresentationCompile
    ]


testRoundtripTerms :: Assertion
testRoundtripTerms = do
  let sig = sigBasic
  let vx = Var (ScopeId "tele:x") 0
  let vy = Var (ScopeId "tele:y") 1
  let tele0 = []
  let tele1 = [Binder vx objSort]
  let tele2 = [Binder vx objSort, Binder vy objSort]
  let x = mkVar objSort vx
  let y = mkVar objSort vy
  let a = mkTerm sig "a" []
  let m x0 y0 = mkTerm sig "m" [x0, y0]
  let f x0 = mkTerm sig "f" [x0]
  let idt x0 = mkTerm sig "id" [x0]
  let cases =
        [ ("var", tele1, x)
        , ("const", tele0, a)
        , ("dup", tele1, m x x)
        , ("reorder", tele2, m y x)
        , ("dependent", tele1, idt x)
        , ("nested", tele2, f (m x y))
        ]
  forM_ cases $ \(label, tele, term) -> do
    diag <-
      case compileTermToDiagram sig cartMode tele term of
        Left err -> assertFailure (label <> ": compile failed: " <> show err)
        Right d -> pure d
    roundtrip <-
      case diagramToTerm1 sig tele diag of
        Left err -> assertFailure (label <> ": readback failed: " <> show err)
        Right t -> pure t
    roundtrip @?= term


testPresentationCompile :: Assertion
testPresentationCompile = do
  let scope1 = ScopeId "eq:r1"
  let vx = Var scope1 0
  let x = mkVar objSort vx
  let eq1 =
        Equation
          { eqName = "r1"
          , eqClass = Computational
          , eqOrient = LR
          , eqTele = [Binder vx objSort]
          , eqLHS = mkTerm sigBasic "f" [x]
          , eqRHS = mkTerm sigBasic "g" [x]
          }
  let eq2 =
        Equation
          { eqName = "r2"
          , eqClass = Computational
          , eqOrient = LR
          , eqTele = []
          , eqLHS = mkTerm sigBasic "a" []
          , eqRHS = mkTerm sigBasic "b" []
          }
  let pres = Presentation "P" sigBasic [eq1, eq2]
  doc <-
    case compilePresentationToDoctrine2 pres of
      Left err -> assertFailure ("compilePresentationToDoctrine2 failed: " <> show err)
      Right d -> pure d
  length (d2Cells2 doc) @?= 2
  let eqMap = M.fromList [(eqName eq1, eq1), (eqName eq2, eq2)]
  forM_ (d2Cells2 doc) $ \cell -> do
    case M.lookup (c2Name cell) eqMap of
      Nothing -> assertFailure "unexpected cell name"
      Just eq -> do
        lhs <-
          case diagramToTerm1 sigBasic (eqTele eq) (c2LHS cell) of
            Left err -> assertFailure ("lhs readback failed: " <> show err)
            Right t -> pure t
        rhs <-
          case diagramToTerm1 sigBasic (eqTele eq) (c2RHS cell) of
            Left err -> assertFailure ("rhs readback failed: " <> show err)
            Right t -> pure t
        lhs @?= eqLHS eq
        rhs @?= eqRHS eq
