{-# LANGUAGE OverloadedStrings #-}
module Test.Kernel.Include
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.Kernel.DSL.Parse (parseRawFile)
import Strat.Kernel.DSL.Elab (elabRawFile)
import Strat.Frontend.Env (ModuleEnv(..))
import Strat.Kernel.Presentation (Presentation(..))
import Strat.Kernel.Signature (Signature(..))
import Strat.Kernel.Syntax (SortName(..), OpName(..))
import qualified Data.Map.Strict as M
import qualified Data.Text as T


tests :: TestTree
tests =
  testGroup
    "Kernel.Include"
    [ testCase "include merges symbols" testIncludeMerges
    , testCase "extends sugar includes base" testExtendsSugar
    , testCase "include duplicate equation idempotent" testIncludeEqIdempotent
    , testCase "include duplicate equation mismatch fails" testIncludeEqMismatch
    ]


testIncludeMerges :: Assertion
testIncludeMerges = do
  let src = T.unlines
        [ "doctrine Base where {"
        , "  sort Obj;"
        , "  op a : Obj;"
        , "}"
        , "doctrine Ext where {"
        , "  include Base;"
        , "  op b : Obj;"
        , "}"
        ]
  case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err)
        Right env ->
          case M.lookup "Ext" (mePresentations env) of
            Nothing -> assertFailure "missing Ext presentation"
            Just pres -> do
              let sig = presSig pres
              assertBool "included sort" (M.member (SortName "Obj") (sigSortCtors sig))
              assertBool "included op a" (M.member (OpName "a") (sigOps sig))
              assertBool "local op b" (M.member (OpName "b") (sigOps sig))


testExtendsSugar :: Assertion
testExtendsSugar = do
  let src = T.unlines
        [ "doctrine Base where {"
        , "  sort Obj;"
        , "  op a : Obj;"
        , "}"
        , "doctrine Ext extends Base where {"
        , "  op b : Obj;"
        , "}"
        ]
  case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err)
        Right env ->
          case M.lookup "Ext" (mePresentations env) of
            Nothing -> assertFailure "missing Ext presentation"
            Just pres -> do
              let sig = presSig pres
              assertBool "included sort" (M.member (SortName "Obj") (sigSortCtors sig))
              assertBool "included op a" (M.member (OpName "a") (sigOps sig))
              assertBool "local op b" (M.member (OpName "b") (sigOps sig))


testIncludeEqIdempotent :: Assertion
testIncludeEqIdempotent = do
  let src = T.unlines
        [ "doctrine Base where {"
        , "  sort Obj;"
        , "  op a : Obj;"
        , "  op f : (x:Obj) -> Obj;"
        , "  computational r : (x:Obj) |- f(?x) -> ?x;"
        , "}"
        , "doctrine Ext where {"
        , "  include Base;"
        , "  computational r : (x:Obj) |- f(?x) -> ?x;"
        , "}"
        ]
  case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err)
        Right env ->
          case M.lookup "Ext" (mePresentations env) of
            Nothing -> assertFailure "missing Ext presentation"
            Just pres -> length (presEqs pres) @?= 1


testIncludeEqMismatch :: Assertion
testIncludeEqMismatch = do
  let src = T.unlines
        [ "doctrine Base where {"
        , "  sort Obj;"
        , "  op a : Obj;"
        , "  op f : (x:Obj) -> Obj;"
        , "  computational r : (x:Obj) |- f(?x) -> ?x;"
        , "}"
        , "doctrine Ext where {"
        , "  include Base;"
        , "  computational r : (x:Obj) |- f(?x) -> a;"
        , "}"
        ]
  case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left _ -> pure ()
        Right _ -> assertFailure "expected duplicate equation name error"
