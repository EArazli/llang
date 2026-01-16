{-# LANGUAGE OverloadedStrings #-}
module Test.Kernel.Sogat
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.Kernel.DSL.Parse (parseRawFile)
import Strat.Kernel.DSL.Elab (elabRawFile)
import Strat.Frontend.Env (ModuleEnv(..))
import Strat.Kernel.Presentation (Presentation(..))
import Strat.Kernel.Signature (Signature(..), SortCtor(..), OpDecl(..))
import Strat.Kernel.Syntax (SortName(..), OpName(..))
import qualified Data.Map.Strict as M
import qualified Data.Text as T


tests :: TestTree
tests =
  testGroup
    "Kernel.Sogat"
    [ testCase "sogat elaborates" testSogatElab
    , testCase "sogat v1 restriction" testSogatRestriction
    ]


testSogatElab :: Assertion
testSogatElab = do
  let src = T.unlines
        [ "sogat STLC where {"
        , "  context_sort Ty;"
        , "  sort Ty;"
        , "  sort Tm (A:Ty);"
        , "  op Arr (A:Ty) (B:Ty) -> Ty;"
        , "  op Lam (A:Ty) (B:Ty) (t: Tm(B) [x:A]) -> Tm(Arr(A,B));"
        , "  op App (A:Ty) (B:Ty) (f:Tm(Arr(A,B))) (u:Tm(A)) -> Tm(B);"
        , "}"
        ]
  case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err)
        Right env ->
          case M.lookup "STLC" (mePresentations env) of
            Nothing -> assertFailure "missing STLC presentation"
            Just pres -> do
              let sig = presSig pres
              assertBool "Ctx sort present" (M.member (SortName "Ctx") (sigSortCtors sig))
              case M.lookup (SortName "Ty") (sigSortCtors sig) of
                Nothing -> assertFailure "missing Ty sort ctor"
                Just ctor -> length (scTele ctor) @?= 1
              case M.lookup (SortName "Tm") (sigSortCtors sig) of
                Nothing -> assertFailure "missing Tm sort ctor"
                Just ctor -> length (scTele ctor) @?= 2
              case M.lookup (OpName "Lam") (sigOps sig) of
                Nothing -> assertFailure "missing Lam op"
                Just op -> length (opTele op) @?= 4


testSogatRestriction :: Assertion
testSogatRestriction = do
  let src = T.unlines
        [ "sogat Bad where {"
        , "  context_sort Ty;"
        , "  sort Ty;"
        , "  sort Tm (A:Ty);"
        , "  op Arr (A:Ty) (B:Ty) -> Ty;"
        , "  op Bad (A:Ty) (B:Ty) (t: Tm(B) [x:A]) -> Tm(Arr(A,x));"
        , "}"
        ]
  case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertBool "expected restriction error" ("SOGAT_V1_DependentTypeNotSupported" `T.isInfixOf` err)
        Right _ -> assertFailure "expected SOGAT restriction failure"
