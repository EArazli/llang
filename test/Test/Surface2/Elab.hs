{-# LANGUAGE OverloadedStrings #-}
module Test.Surface2.Elab
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.Surface2.Elab
import Strat.Kernel.DSL.AST


tests :: TestTree
tests =
  testGroup
    "Surface2.Elab"
    [ testCase "judgment sort must exist" testJudgSort
    , testCase "judgment output arity mismatch in conclusion" testJudgOutputMismatchConclusion
    , testCase "judgment output arity mismatch in premise" testJudgOutputMismatchPremise
    ]


testJudgSort :: Assertion
testJudgSort = do
  let decl =
        RawSurfaceDecl
          { rsdName = "BadSort"
          , rsdItems =
              [ RSRequiresInterface "CCC"
              , RSContextSort "Ty"
              , RSSort "Ty"
              , RSJudg (RawSurfaceJudg "HasType" [RawSurfaceJudgParam "t" "TmTypo"] [])
              ]
          }
  case elabSurfaceDecl decl of
    Left _ -> pure ()
    Right _ -> assertFailure "expected unknown sort error"


testJudgOutputMismatchConclusion :: Assertion
testJudgOutputMismatchConclusion = do
  let judg =
        RawSurfaceJudg
          { rsjName = "HasType"
          , rsjParams =
              [ RawSurfaceJudgParam "G" "Ctx"
              , RawSurfaceJudgParam "t" "Tm"
              , RawSurfaceJudgParam "A" "Ty"
              ]
          , rsjOutputs = [RawSurfaceJudgParam "e" "Core"]
          }
  let rule =
        RawSurfaceRule
          { rsrName = "bad"
          , rsrPremises = []
          , rsrConclusion =
              RawSurfaceConclusion
                { rcoName = "HasType"
                , rcoArgs = [RSPVar "G", RSPVar "t", RSPVar "A"]
                , rcoOutputs = []
                }
          }
  let decl =
        RawSurfaceDecl
          { rsdName = "BadOut"
          , rsdItems =
              [ RSRequiresInterface "CCC"
              , RSContextSort "Ty"
              , RSSort "Ty"
              , RSSort "Tm"
              , RSJudg judg
              , RSRule rule
              ]
          }
  case elabSurfaceDecl decl of
    Left _ -> pure ()
    Right _ -> assertFailure "expected output arity mismatch"


testJudgOutputMismatchPremise :: Assertion
testJudgOutputMismatchPremise = do
  let judg =
        RawSurfaceJudg
          { rsjName = "HasType"
          , rsjParams =
              [ RawSurfaceJudgParam "G" "Ctx"
              , RawSurfaceJudgParam "t" "Tm"
              , RawSurfaceJudgParam "A" "Ty"
              ]
          , rsjOutputs = [RawSurfaceJudgParam "e" "Core"]
          }
  let prem =
        RPremiseJudg
          { rpjName = "HasType"
          , rpjArgs = [RSPVar "G", RSPVar "t", RSPVar "A"]
          , rpjOutputs = []
          , rpjUnder = Nothing
          }
  let rule =
        RawSurfaceRule
          { rsrName = "badPrem"
          , rsrPremises = [prem]
          , rsrConclusion =
              RawSurfaceConclusion
                { rcoName = "HasType"
                , rcoArgs = [RSPVar "G", RSPVar "t", RSPVar "A"]
                , rcoOutputs = [RCEVar "e"]
                }
          }
  let decl =
        RawSurfaceDecl
          { rsdName = "BadPrem"
          , rsdItems =
              [ RSRequiresInterface "CCC"
              , RSContextSort "Ty"
              , RSSort "Ty"
              , RSSort "Tm"
              , RSJudg judg
              , RSRule rule
              ]
          }
  case elabSurfaceDecl decl of
    Left _ -> pure ()
    Right _ -> assertFailure "expected premise output arity mismatch"
