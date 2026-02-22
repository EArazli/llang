{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.UnifyObj
  ( tests
  ) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.Obj
  ( Obj(..)
  , ObjName(..)
  , ObjRef(..)
  , ObjVar(..)
  , ObjArg(..)
  , TermDiagram(..)
  )
import Strat.Poly.TypeTheory (TypeTheory(..), TypeParamSig(..), modeOnlyTypeTheory)
import Strat.Poly.UnifyObj (emptySubst, unifyObjFlex)
import Strat.Poly.Diagram (idDTm)
import Test.Poly.Helpers (mkModes)


tests :: TestTree
tests =
  testGroup
    "Poly.UnifyObj"
    [ testCase "occurs check sees object variables inside term arguments" testOccursObjVarInTermArg
    ]

testOccursObjVarInTermArg :: Assertion
testOccursObjVarInTermArg = do
  let mode = ModeName "M"
      aVar = ObjVar { ovName = "a", ovMode = mode }
      sortTy = OVar aVar
      fooRef = ObjRef mode (ObjName "Foo")
      tm = TermDiagram (idDTm mode [sortTy] [sortTy])
      rhs = OCon fooRef [OATm tm]
      ttBase = modeOnlyTypeTheory (mkModes [mode])
      tt =
        ttBase
          { ttObjParams = M.singleton fooRef [TPS_Tm sortTy]
          }
  case unifyObjFlex tt [sortTy] (S.singleton aVar) S.empty emptySubst (OVar aVar) rhs of
    Left _ -> pure ()
    Right _ -> assertFailure "expected occurs-check failure"
