{-# LANGUAGE OverloadedStrings #-}
module Test.Kernel.Regression
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.Kernel.Presentation
import Strat.Kernel.Rule (Equation(..))
import Strat.Kernel.Rewrite (normalize)
import Strat.Kernel.RewriteSystem
import Strat.Kernel.Morphism (joinableWithin)
import Strat.Kernel.Syntax
import Strat.Kernel.Term
import Strat.Kernel.Types
import Data.Text (Text)
import qualified Data.Text as T
import Test.Kernel.Fixtures
import Control.Monad (forM_)


tests :: TestTree
tests =
  testGroup
    "Kernel.Regression"
    [ testCase "normalize regression" testNormalizeRegression
    , testCase "joinableWithin regression" testJoinableRegression
    ]

mkEqConst :: Text -> Text -> Text -> Equation
mkEqConst name lhs rhs =
  Equation
    { eqName = name
    , eqClass = Computational
    , eqOrient = LR
    , eqTele = []
    , eqLHS = mkTerm sigBasic lhs []
    , eqRHS = mkTerm sigBasic rhs []
    }

mkEqUnary :: Text -> Text -> Text -> Equation
mkEqUnary name lhsOp rhsOp =
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

mkEqUnitL :: Equation
mkEqUnitL =
  let scope = ScopeId "eq:unitL"
      vx = Var scope 0
      x = mkVar objSort vx
      a = mkTerm sigBasic "a" []
  in Equation
      { eqName = "unitL"
      , eqClass = Computational
      , eqOrient = LR
      , eqTele = [Binder vx objSort]
      , eqLHS = mkTerm sigBasic "m" [a, x]
      , eqRHS = x
      }

mkEqUnitR :: Equation
mkEqUnitR =
  let scope = ScopeId "eq:unitR"
      vx = Var scope 0
      x = mkVar objSort vx
      a = mkTerm sigBasic "a" []
  in Equation
      { eqName = "unitR"
      , eqClass = Computational
      , eqOrient = LR
      , eqTele = [Binder vx objSort]
      , eqLHS = mkTerm sigBasic "m" [x, a]
      , eqRHS = x
      }

mkEqAssoc :: Equation
mkEqAssoc =
  let scope = ScopeId "eq:assoc"
      vx = Var scope 0
      vy = Var scope 1
      vz = Var scope 2
      x = mkVar objSort vx
      y = mkVar objSort vy
      z = mkVar objSort vz
  in Equation
      { eqName = "assoc"
      , eqClass = Computational
      , eqOrient = LR
      , eqTele = [Binder vx objSort, Binder vy objSort, Binder vz objSort]
      , eqLHS = mkTerm sigBasic "m" [mkTerm sigBasic "m" [x, y], z]
      , eqRHS = mkTerm sigBasic "m" [x, mkTerm sigBasic "m" [y, z]]
      }

mkRS :: RewriteSystem
mkRS =
  case compileRewriteSystem UseAllOriented (Presentation "P" sigBasic eqs) of
    Left err -> error (T.unpack err)
    Right rs -> rs
  where
    eqs =
      [ mkEqConst "r1" "a" "b"
      , mkEqConst "r2" "b" "c"
      , mkEqUnary "r3" "f" "g"
      , mkEqUnitL
      , mkEqUnitR
      , mkEqAssoc
      ]

termCases :: [(Text, Term, Term)]
termCases =
  let a = mkTerm sigBasic "a" []
      b = mkTerm sigBasic "b" []
      c = mkTerm sigBasic "c" []
      f x = mkTerm sigBasic "f" [x]
      g x = mkTerm sigBasic "g" [x]
      k x = mkTerm sigBasic "k" [x]
      m x y = mkTerm sigBasic "m" [x, y]
  in
    [ ("a", a, c)
    , ("b", b, c)
    , ("f(a)", f a, g c)
    , ("m(a,b)", m a b, c)
    , ("m(b,a)", m b a, c)
    , ("m(m(a,b),c)", m (m a b) c, m c c)
    , ("m(k(a),a)", m (k a) a, k c)
    , ("g(k(a))", g (k a), g (k c))
    , ("m(f(a),a)", m (f a) a, g c)
    , ("m(a,m(a,a))", m a (m a a), c)
    , ("k(b)", k b, k c)
    ]

joinableCases :: [(Text, Term, Term, Bool)]
joinableCases =
  let a = mkTerm sigBasic "a" []
      b = mkTerm sigBasic "b" []
      c = mkTerm sigBasic "c" []
      f x = mkTerm sigBasic "f" [x]
      g x = mkTerm sigBasic "g" [x]
      h x = mkTerm sigBasic "h" [x]
      k x = mkTerm sigBasic "k" [x]
      m x y = mkTerm sigBasic "m" [x, y]
  in
    [ ("a vs c", a, c, True)
    , ("f(a) vs g(c)", f a, g c, True)
    , ("k(a) vs k(c)", k a, k c, True)
    , ("m(a,b) vs b", m a b, b, True)
    , ("g(a) vs k(a)", g a, k a, False)
    , ("g(a) vs h(a)", g a, h a, False)
    ]


testNormalizeRegression :: Assertion
testNormalizeRegression = do
  let rs = mkRS
  forM_ termCases $ \(label, term, expected) ->
    assertEqual (T.unpack label) expected (normalize 50 rs term)


testJoinableRegression :: Assertion
testJoinableRegression = do
  let rs = mkRS
  forM_ joinableCases $ \(label, t1, t2, expected) ->
    assertEqual (T.unpack label) expected (joinableWithin 50 rs t1 t2)
