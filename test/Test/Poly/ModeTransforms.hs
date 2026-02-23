{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.ModeTransforms
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Map.Strict as M
import qualified Data.Text as T

import Strat.DSL.Parse (parseRawFile)
import Strat.DSL.Elab (elabRawFile)
import Strat.Frontend.Env (ModuleEnv(..))
import Strat.Poly.Doctrine (Doctrine(..))
import Strat.Poly.ModeTheory
  ( ModExpr(..)
  , ModeName(..)
  , ModName(..)
  , ModTransformName(..)
  , mtdFrom
  , mtdTo
  , mtdWitness
  , mtTransforms
  )
import Strat.Poly.Names (GenName(..))


tests :: TestTree
tests =
  testGroup
    "Poly.ModeTransforms"
    [ testCase "parse + elab stores mod_transform with default witness" testModTransformParseElab
    , testCase "mod_transform rejects mismatched endpoints" testModTransformRejectEndpoints
    , testCase "mod_transform rejects invalid witness signature" testModTransformRejectWitnessShape
    ]


testModTransformParseElab :: Assertion
testModTransformParseElab = do
  let src =
        T.unlines
          [ "doctrine Adj where {"
          , "  mode C classifiedBy C via C.U_C;"
          , "  type U_C @C;"
          , "  mode D classifiedBy D via D.U_D;"
          , "  type U_D @D;"
          , "  modality F : C -> D;"
          , "  modality U : D -> C;"
          , "  gen eta(a@C) : [a] -> [U.F(a)] @C;"
          , "  mod_transform eta : id@C => U.F;"
          , "}"
          ]
  env <- requireEither (parseRawFile src >>= elabRawFile)
  doc <- requireDoctrine env "Adj"
  tr <-
    case M.lookup (ModTransformName "eta") (mtTransforms (dModes doc)) of
      Nothing -> assertFailure "missing mode transform eta" >> fail "unreachable"
      Just decl -> pure decl
  mtdFrom tr @?= ModExpr { meSrc = ModeName "C", meTgt = ModeName "C", mePath = [] }
  mtdTo tr @?= ModExpr { meSrc = ModeName "C", meTgt = ModeName "C", mePath = [ModName "F", ModName "U"] }
  mtdWitness tr @?= GenName "eta"


testModTransformRejectEndpoints :: Assertion
testModTransformRejectEndpoints = do
  let src =
        T.unlines
          [ "doctrine Bad where {"
          , "  mode C classifiedBy C via C.U_C;"
          , "  type U_C @C;"
          , "  mode D classifiedBy D via D.U_D;"
          , "  type U_D @D;"
          , "  modality F : C -> D;"
          , "  modality U : D -> C;"
          , "  mod_transform bad : F => U;"
          , "}"
          ]
  err <- requireElabError src
  assertBool "expected endpoint mismatch error" ("source/target mismatch" `T.isInfixOf` err)


testModTransformRejectWitnessShape :: Assertion
testModTransformRejectWitnessShape = do
  let src =
        T.unlines
          [ "doctrine Wrong where {"
          , "  mode C classifiedBy C via C.U_C;"
          , "  type U_C @C;"
          , "  mode D classifiedBy D via D.U_D;"
          , "  type U_D @D;"
          , "  modality F : C -> D;"
          , "  modality U : D -> C;"
          , "  gen etaBad(a@C) : [U.F(a), U.F(a)] -> [U.F(a)] @C;"
          , "  mod_transform eta : id@C => U.F witness etaBad;"
          , "}"
          ]
  err <- requireElabError src
  assertBool "expected witness shape error" ("witness generator domain" `T.isInfixOf` err)


requireElabError :: T.Text -> IO T.Text
requireElabError src =
  case parseRawFile src >>= elabRawFile of
    Left err -> pure err
    Right _ -> assertFailure "expected elaboration failure" >> fail "unreachable"


requireEither :: Either T.Text a -> IO a
requireEither mv =
  case mv of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right v -> pure v


requireDoctrine :: ModuleEnv -> T.Text -> IO Doctrine
requireDoctrine env name =
  case M.lookup name (meDoctrines env) of
    Nothing -> assertFailure ("missing doctrine: " <> T.unpack name) >> fail "unreachable"
    Just doc -> pure doc
