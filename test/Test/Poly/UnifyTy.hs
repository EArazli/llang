{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.UnifyTy
  ( tests
  ) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.TypeExpr
  ( TypeExpr(..)
  , TypeName(..)
  , TypeRef(..)
  , TyVar(..)
  , TypeArg(..)
  , TermDiagram(..)
  )
import Strat.Poly.TypeTheory (TypeTheory(..), TypeParamSig(..), modeOnlyTypeTheory)
import Strat.Poly.UnifyTy (emptySubst, unifyTyFlex)
import Strat.Poly.Diagram (idDTm)
import Test.Poly.Helpers (mkModes)


tests :: TestTree
tests =
  testGroup
    "Poly.UnifyTy"
    [ testCase "occurs check sees type variables inside term arguments" testOccursTyVarInTermArg
    ]

testOccursTyVarInTermArg :: Assertion
testOccursTyVarInTermArg = do
  let mode = ModeName "M"
      aVar = TyVar { tvName = "a", tvMode = mode }
      sortTy = TVar aVar
      fooRef = TypeRef mode (TypeName "Foo")
      tm = TermDiagram (idDTm mode [sortTy] [sortTy])
      rhs = TCon fooRef [TATm tm]
      ttBase = modeOnlyTypeTheory (mkModes [mode])
      tt =
        ttBase
          { ttTypeParams = M.singleton fooRef [TPS_Tm sortTy]
          }
  case unifyTyFlex tt [sortTy] (S.singleton aVar) S.empty emptySubst (TVar aVar) rhs of
    Left _ -> pure ()
    Right _ -> assertFailure "expected occurs-check failure"
