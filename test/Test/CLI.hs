{-# LANGUAGE OverloadedStrings #-}
module Test.CLI
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.CLI
import Strat.Backend (Value(..))
import Strat.Backend.Concat (CatExpr(..))
import Strat.Kernel.RewriteSystem (RewritePolicy(..))
import Strat.Kernel.Syntax
import qualified Data.Text as T
import Paths_llang (getDataFileName)


tests :: TestTree
tests =
  testGroup
    "CLI"
    [ testCase "end-to-end monoid" testEndToEndMonoid
    , testCase "end-to-end monoid string model" testEndToEndMonoidString
    , testCase "end-to-end category" testEndToEndCat
    , testCase "end-to-end peano nat model" testEndToEndPeano
    , testCase "end-to-end lambda to SKI" testEndToEndSKI
    ]


testEndToEndMonoid :: Assertion
testEndToEndMonoid = do
  path <- getDataFileName "examples/monoid.llang"
  let opts =
        CLIOptions
          { optFile = path
          , optDoctrine = "Combined"
          , optTerm = "C.k(C.m(C.e,C.e))"
          , optFuel = 5
          , optPolicy = UseOnlyComputationalLR
          , optLang = LangComb
          , optModel = ModelSymbolic
          }
  result <- runCLI opts
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> do
      crCatExpr out @?= CatOp (OpName "C.e") []
      crValue out @?= VAtom "C.e"
      termSort (crNormalized out) @?= Sort (SortName "C.Obj") []
      assertBool "normalized differs from input" (crNormalized out /= crInputTerm out)

testEndToEndMonoidString :: Assertion
testEndToEndMonoidString = do
  path <- getDataFileName "examples/monoid.llang"
  let opts =
        CLIOptions
          { optFile = path
          , optDoctrine = "Combined"
          , optTerm = "C.m(C.x,C.y)"
          , optFuel = 5
          , optPolicy = UseOnlyComputationalLR
          , optLang = LangComb
          , optModel = ModelString
          }
  result <- runCLI opts
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> crValue out @?= VString "xy"


testEndToEndCat :: Assertion
testEndToEndCat = do
  path <- getDataFileName "examples/cat.llang"
  let opts =
        CLIOptions
          { optFile = path
          , optDoctrine = "Cat"
          , optTerm = "C.comp(C.A,C.B,C.D, C.comp(C.B,C.C,C.D, C.h, C.g), C.comp(C.A,C.A,C.B, C.f, C.id(C.A)))"
          , optFuel = 40
          , optPolicy = UseOnlyComputationalLR
          , optLang = LangComb
          , optModel = ModelSymbolic
          }
  result <- runCLI opts
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> do
      let ops = collectOps (crNormalized out)
      assertBool "no id in normal form" (OpName "C.id" `notElem` ops)
      case termNode (crNormalized out) of
        TOp (OpName "C.comp") [_, _, _, Term _ (TOp (OpName "C.h") []), Term _ (TOp (OpName "C.comp") innerArgs)] ->
          case innerArgs of
            [_, _, _, Term _ (TOp (OpName "C.g") []), Term _ (TOp (OpName "C.f") [])] -> pure ()
            _ -> assertFailure "inner composition not in expected form"
        _ -> assertFailure "outer composition not in expected form"


testEndToEndPeano :: Assertion
testEndToEndPeano = do
  path <- getDataFileName "examples/peano.llang"
  let opts =
        CLIOptions
          { optFile = path
          , optDoctrine = "Nat"
          , optTerm = "mul(S(S(Z)), add(S(Z), S(S(Z))))"
          , optFuel = 200
          , optPolicy = UseOnlyComputationalLR
          , optLang = LangComb
          , optModel = ModelNat
          }
  result <- runCLI opts
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> crValue out @?= VInt 6


testEndToEndSKI :: Assertion
testEndToEndSKI = do
  path <- getDataFileName "examples/ski.llang"
  let opts =
        CLIOptions
          { optFile = path
          , optDoctrine = "SKI"
          , optTerm = "(\\x.\\y. x) a b"
          , optFuel = 80
          , optPolicy = UseOnlyComputationalLR
          , optLang = LangLambda
          , optModel = ModelSymbolic
          }
  result <- runCLI opts
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> crValue out @?= VAtom "SKI.a"

collectOps :: Term -> [OpName]
collectOps tm =
  case termNode tm of
    TVar _ -> []
    TOp op args -> op : concatMap collectOps args
