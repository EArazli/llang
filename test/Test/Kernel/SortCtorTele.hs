{-# LANGUAGE OverloadedStrings #-}
module Test.Kernel.SortCtorTele
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.Kernel.DSL.Parse (parseRawFile)
import Strat.Kernel.DSL.Elab (elabRawFile)
import Strat.Kernel.Presentation (validatePresentation)
import Strat.Frontend.Env (ModuleEnv(..))
import qualified Data.Map.Strict as M
import qualified Data.Text as T


tests :: TestTree
tests =
  testGroup
    "Kernel.SortCtorTele"
    [ testCase "dependent sort ctor telescope" testSortCtorTele
    ]


testSortCtorTele :: Assertion
testSortCtorTele = do
  let src = T.unlines
        [ "doctrine Dep where {"
        , "  sort Ctx;"
        , "  sort Ty (Γ:Ctx);"
        , "  sort Tm (Γ:Ctx) (A:Ty(?Γ));"
        , "  op id : (Γ:Ctx) (A:Ty(?Γ)) (x:Tm(?Γ, ?A)) -> Tm(?Γ, ?A);"
        , "}"
        ]
  case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err)
        Right env ->
          case M.lookup "Dep" (meDoctrines env) of
            Nothing -> assertFailure "missing Dep presentation"
            Just pres ->
              case validatePresentation pres of
                Left err -> assertFailure (T.unpack err)
                Right () -> pure ()
