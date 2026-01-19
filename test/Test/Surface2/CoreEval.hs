{-# LANGUAGE OverloadedStrings #-}
module Test.Surface2.CoreEval
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.Surface2.CoreEval
import Strat.Surface2.Def
import Strat.Surface2.Term
import Strat.Kernel.Presentation
import Strat.Kernel.Signature
import qualified Data.Map.Strict as M


tests :: TestTree
tests =
  testGroup
    "Surface2.CoreEval"
    [ testCase "define repeated variable enforces equality" testDefineRepeatedVar
    ]


testDefineRepeatedVar :: Assertion
testDefineRepeatedVar = do
  let def =
        Define
          { defName = "eqTest"
          , defClauses =
              [ DefineClause [DPVar "x", DPVar "x"] (CoreVar "one") []
              , DefineClause [DPVar "x", DPVar "y"] (CoreVar "zero") []
              ]
          }
  let surf =
        SurfaceDef
          { sdName = "Test"
          , sdSorts = M.empty
          , sdContextSort = Sort2Name "Ty"
          , sdCons = M.empty
          , sdJudgments = M.empty
          , sdRules = []
          , sdDefines = M.fromList [("eqTest", def)]
          , sdRequires = [SurfaceRequire "ccc" (Presentation "I" (Signature M.empty M.empty) [])]
          , sdCtxDisc = CtxCartesian
          }
  let pres = Presentation "Test" (Signature M.empty M.empty) []
  let env =
        M.fromList
          [ ("a", CVNat 1)
          , ("b", CVNat 2)
          , ("one", CVNat 1)
          , ("zero", CVNat 0)
          ]
  case evalCoreExpr pres surf M.empty env (CoreApp "eqTest" [CoreVar "a", CoreVar "b"]) of
    Left err -> assertFailure (show err)
    Right result -> result @?= CVNat 0
