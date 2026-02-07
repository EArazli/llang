{-# LANGUAGE OverloadedStrings #-}
module Test.Frontend.Coerce
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Text as T

import Strat.Common.Rules (RewritePolicy(..))
import Strat.Frontend.Coerce (findUniqueCoercionPath)
import Strat.Frontend.Env (ModuleEnv(..), emptyEnv)
import Strat.Frontend.Run (RunResult(..), runWithEnv, selectRun)
import Strat.DSL.Parse (parseRawFile)
import Strat.DSL.Elab (elabRawFile)
import Strat.Poly.Doctrine (Doctrine(..))
import Strat.Poly.ModeTheory (ModeName(..), ModeTheory(..), ModeInfo(..), VarDiscipline(..), mtModes)
import Strat.Poly.Morphism (Morphism(..))
import Test.Poly.Helpers (identityModMap)


tests :: TestTree
tests =
  testGroup
    "Frontend.Coerce"
    [ testCase "ambiguous coercion paths are rejected" testAmbiguousCoercion
    , testCase "model conversion uses coercion paths" testModelCoercion
    ]

modeM :: ModeName
modeM = ModeName "M"

mkDoc :: T.Text -> Doctrine
mkDoc name =
  Doctrine
    { dName = name
    , dModes = mkModes (S.singleton modeM)
    , dAttrSorts = M.empty
    , dTypes = M.fromList [(modeM, M.empty)]
    , dGens = M.empty
    , dCells2 = []
    }

mkModes :: S.Set ModeName -> ModeTheory
mkModes modes =
  ModeTheory
    (M.fromList [ (m, ModeInfo m Linear) | m <- S.toList modes ])
    M.empty
    []
    []

identityModeMap :: Doctrine -> M.Map ModeName ModeName
identityModeMap doc =
  M.fromList [ (m, m) | m <- M.keys (mtModes (dModes doc)) ]

mkCoercion :: T.Text -> Doctrine -> Doctrine -> Morphism
mkCoercion name src tgt =
  Morphism
    { morName = name
    , morSrc = src
    , morTgt = tgt
    , morIsCoercion = True
    , morModeMap = identityModeMap src
    , morModMap = identityModMap src
    , morAttrSortMap = M.empty
    , morTypeMap = M.empty
    , morGenMap = M.empty
    , morPolicy = UseAllOriented
    , morFuel = 10
    }

mkEnvWithCoercions :: ModuleEnv
mkEnvWithCoercions =
  let docA = mkDoc "A"
      docB = mkDoc "B"
      docC = mkDoc "C"
      docD = mkDoc "D"
      morphs =
        [ ("ab", mkCoercion "ab" docA docB)
        , ("bd", mkCoercion "bd" docB docD)
        , ("ac", mkCoercion "ac" docA docC)
        , ("cd", mkCoercion "cd" docC docD)
        ]
      docs =
        [ ("A", docA)
        , ("B", docB)
        , ("C", docC)
        , ("D", docD)
        ]
  in emptyEnv
      { meDoctrines = M.fromList docs
      , meMorphisms = M.fromList morphs
      }

testAmbiguousCoercion :: Assertion
testAmbiguousCoercion =
  case findUniqueCoercionPath mkEnvWithCoercions "A" "D" of
    Right _ -> assertFailure "expected ambiguity"
    Left err -> do
      assertBool "expected ambiguous coercion paths" ("ambiguous coercion paths" `T.isInfixOf` err)
      assertBool "expected first path" ("[ab, bd]" `T.isInfixOf` err)
      assertBool "expected second path" ("[ac, cd]" `T.isInfixOf` err)


testModelCoercion :: Assertion
testModelCoercion = do
  let src = T.unlines
        [ "doctrine Base where {"
        , "  mode M;"
        , "  gen u : [] -> [] @M;"
        , "}"
        , "doctrine Ext extends Base where {"
        , "}"
        , "model M : Ext where {"
        , "  default = symbolic;"
        , "}"
        , "run main where {"
        , "  doctrine Base;"
        , "  model M;"
        , "  show value;"
        , "} ---"
        , "u"
        ]
  env <- case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err)
        Right e -> pure e
  spec <- case selectRun env Nothing of
    Left err -> assertFailure (T.unpack err)
    Right s -> pure s
  result <- case runWithEnv env spec of
    Left err -> assertFailure (T.unpack err)
    Right r -> pure r
  prOutput result @?= "value:\n[]"
