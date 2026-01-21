{-# LANGUAGE OverloadedStrings #-}
module Test.Kernel.Sogat
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.Kernel.DSL.Parse (parseRawFile)
import Strat.Kernel.DSL.Elab (elabRawFile)
import Strat.Frontend.Env (ModuleEnv(..))
import Strat.Kernel.DoctrineExpr (elabDocExpr)
import Strat.Kernel.Presentation (Presentation(..), validatePresentation)
import Strat.Kernel.Signature (Signature(..), SortCtor(..), OpDecl(..))
import Strat.Kernel.Syntax (SortName(..), OpName(..))
import qualified Data.Map.Strict as M
import qualified Data.Text as T


tests :: TestTree
tests =
  testGroup
    "Kernel.Sogat"
    [ testCase "sogat elaborates" testSogatElab
    , testCase "sogat validates after qualification" testSogatQualified
    , testCase "sogat type former with term args" testSogatDependentType
    , testCase "sogat type former with binder arg" testSogatTypeBinder
    , testCase "sogat multi-binder weakening" testSogatMultiBinder
    , testCase "sogat weakening in indices" testSogatWeakIndex
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
              case validatePresentation pres of
                Left err -> assertFailure (T.unpack err)
                Right () -> pure ()
              let sig = presSig pres
              assertBool "Ctx sort present" (M.member (SortName "Ctx") (sigSortCtors sig))
              case M.lookup (SortName "Ty") (sigSortCtors sig) of
                Nothing -> assertFailure "missing Ty sort ctor"
                Just ctor -> length (scTele ctor) @?= 1
              case M.lookup (SortName "Tm") (sigSortCtors sig) of
                Nothing -> assertFailure "missing Tm sort ctor"
                Just ctor -> length (scTele ctor) @?= 2
              case M.lookup (OpName "Arr") (sigOps sig) of
                Nothing -> assertFailure "missing Arr op"
                Just op -> length (opTele op) @?= 3
              case M.lookup (OpName "Lam") (sigOps sig) of
                Nothing -> assertFailure "missing Lam op"
                Just op -> length (opTele op) @?= 4


testSogatQualified :: Assertion
testSogatQualified = do
  let src = T.unlines
        [ "sogat MultiBinder where {"
        , "  context_sort Ty;"
        , "  sort Ty;"
        , "  sort Tm (A:Ty);"
        , "  op Arr (A:Ty) (B:Ty) -> Ty;"
        , "  op Foo (A:Ty) (t: Tm(A) [x:Arr(A,A)] [y:Arr(A,A)]) -> Tm(A);"
        , "}"
        ]
  case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err)
        Right env ->
          case M.lookup "MultiBinder" (meDoctrines env) of
            Nothing -> assertFailure "missing MultiBinder doctrine expr"
            Just dexpr ->
              case elabDocExpr dexpr of
                Left err -> assertFailure (T.unpack err)
                Right presQ ->
                  case validatePresentation presQ of
                    Left err -> assertFailure (T.unpack err)
                    Right () -> pure ()


testSogatDependentType :: Assertion
testSogatDependentType = do
  let src = T.unlines
        [ "sogat Dep where {"
        , "  context_sort Ty;"
        , "  sort Ty;"
        , "  sort Tm (A:Ty);"
        , "  op Id (A:Ty) (x:Tm(A)) (y:Tm(A)) -> Ty;"
        , "}"
        ]
  case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err)
        Right env -> do
          case M.lookup "Dep" (mePresentations env) of
            Nothing -> assertFailure "missing Dep presentation"
            Just pres ->
              case validatePresentation pres of
                Left err -> assertFailure (T.unpack err)
                Right () -> pure ()

testSogatTypeBinder :: Assertion
testSogatTypeBinder = do
  let src = T.unlines
        [ "sogat Pi where {"
        , "  context_sort Ty;"
        , "  sort Ty;"
        , "  sort Tm (A:Ty);"
        , "  op Pi (A:Ty) (B:Ty [x:A]) -> Ty;"
        , "}"
        ]
  case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err)
        Right env -> do
          case M.lookup "Pi" (mePresentations env) of
            Nothing -> assertFailure "missing Pi presentation"
            Just pres ->
              case validatePresentation pres of
                Left err -> assertFailure (T.unpack err)
                Right () -> pure ()

testSogatMultiBinder :: Assertion
testSogatMultiBinder = do
  let src = T.unlines
        [ "sogat MultiBinder where {"
        , "  context_sort Ty;"
        , "  sort Ty;"
        , "  sort Tm (A:Ty);"
        , "  op Arr (A:Ty) (B:Ty) -> Ty;"
        , "  op Foo (A:Ty) (t: Tm(A) [x:Arr(A,A)] [y:Arr(A,A)]) -> Tm(A);"
        , "}"
        ]
  case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err)
        Right env -> do
          case M.lookup "MultiBinder" (mePresentations env) of
            Nothing -> assertFailure "missing MultiBinder presentation"
            Just pres ->
              case validatePresentation pres of
                Left err -> assertFailure (T.unpack err)
                Right () -> pure ()

testSogatWeakIndex :: Assertion
testSogatWeakIndex = do
  let src = T.unlines
        [ "sogat WeakIndex where {"
        , "  context_sort Ty;"
        , "  sort Ty;"
        , "  sort Tm (A:Ty);"
        , "  sort Pack (A:Ty) (u:Tm(A));"
        , "  op Foo (A:Ty) (u:Tm(A)) (p:Pack(A,u) [x:A]) -> Tm(A);"
        , "}"
        ]
  case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err)
        Right env -> do
          case M.lookup "WeakIndex" (mePresentations env) of
            Nothing -> assertFailure "missing WeakIndex presentation"
            Just pres ->
              case validatePresentation pres of
                Left err -> assertFailure (T.unpack err)
                Right () -> pure ()
