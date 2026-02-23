{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
module Test.Poly.UnifyObj
  ( tests
  ) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.Obj
  ( ObjName(..)
  , ObjRef(..)
  , ObjVar(..)
  , pattern OATm
  , TermDiagram(..)
  , pattern OVar
  , pattern OCon
  , occursObjVar
  )
import Strat.Poly.Diagram (idDTm)


tests :: TestTree
tests =
  testGroup
    "Poly.UnifyObj"
    [ testCase "occursObjVar ignores variables inside term arguments" testIgnoresObjVarInTermArg
    ]

testIgnoresObjVarInTermArg :: Assertion
testIgnoresObjVarInTermArg = do
  let mode = ModeName "M"
      aVar = ObjVar { ovName = "a", ovMode = mode }
      fooRef = ObjRef mode (ObjName "Foo")
      tm = TermDiagram (idDTm mode [OVar aVar] [OVar aVar])
      rhs = OCon fooRef [OATm tm]
  assertBool "object occurs check should ignore CATm payloads" (not (occursObjVar aVar rhs))
