{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.Coherence
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.ModeTheory (ModeName(..), ModeTheory(..))
import Strat.Poly.TypeExpr (TypeExpr(..), TypeName(..), TypeRef(..))
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Diagram (genD)
import Strat.Poly.Graph (Diagram)
import Strat.Poly.Doctrine (Doctrine(..), GenDecl(..), TypeSig(..), validateDoctrine)
import Strat.Poly.Cell2 (Cell2(..))
import Strat.Poly.Coherence (checkCoherence, ObligationResult(..))
import Strat.Poly.CriticalPairs (CPMode(..))
import Strat.Common.Rules (RewritePolicy(..), Orientation(..), RuleClass(..))


tests :: TestTree
tests =
  testGroup
    "Poly.Coherence"
    [ testCase "coherence joinable system succeeds" testCoherenceJoinable
    , testCase "coherence detects non-joinable system" testCoherenceFails
    ]

require :: Either Text a -> IO a
require = either (assertFailure . T.unpack) pure

modeName :: ModeName
modeName = ModeName "M"

aTy :: TypeExpr
aTy = TCon (TypeRef modeName (TypeName "A")) []

mkGenDecl :: Text -> GenDecl
mkGenDecl name =
  GenDecl
    { gdName = GenName name
    , gdMode = modeName
    , gdTyVars = []
    , gdDom = [aTy]
    , gdCod = [aTy]
    , gdAttrs = []
    }

mkCell :: Text -> Diagram -> Diagram -> Cell2
mkCell name lhs rhs =
  Cell2
    { c2Name = name
    , c2Class = Computational
    , c2Orient = LR
    , c2TyVars = []
    , c2LHS = lhs
    , c2RHS = rhs
    }

mkDoctrine :: [Cell2] -> Doctrine
mkDoctrine cells =
  let gens =
        [ mkGenDecl "f"
        , mkGenDecl "g"
        , mkGenDecl "h"
        , mkGenDecl "k"
        ]
  in Doctrine
      { dName = "D"
      , dModes = ModeTheory (S.singleton modeName) M.empty []
      , dTypes = M.fromList [(modeName, M.fromList [(TypeName "A", TypeSig [])])]
      , dGens = M.fromList [(modeName, M.fromList [(gdName g, g) | g <- gens])]
      , dCells2 = cells
      , dAttrSorts = M.empty
      }

testCoherenceJoinable :: Assertion
testCoherenceJoinable = do
  f <- require (genD modeName [aTy] [aTy] (GenName "f"))
  g <- require (genD modeName [aTy] [aTy] (GenName "g"))
  h <- require (genD modeName [aTy] [aTy] (GenName "h"))
  k <- require (genD modeName [aTy] [aTy] (GenName "k"))
  let cells =
        [ mkCell "r1" f g
        , mkCell "r2" f h
        , mkCell "r3" g k
        , mkCell "r4" h k
        ]
  let doc = mkDoctrine cells
  case validateDoctrine doc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  res <- case checkCoherence CP_All UseAllOriented 3 doc of
    Left err -> assertFailure (T.unpack err)
    Right r -> pure r
  assertBool "expected all obligations satisfied" (all hasWitness res)
  where
    hasWitness r = case orWitness r of
      Nothing -> False
      Just _ -> True

testCoherenceFails :: Assertion
testCoherenceFails = do
  f <- require (genD modeName [aTy] [aTy] (GenName "f"))
  g <- require (genD modeName [aTy] [aTy] (GenName "g"))
  h <- require (genD modeName [aTy] [aTy] (GenName "h"))
  let cells =
        [ mkCell "r1" f g
        , mkCell "r2" f h
        ]
  let doc = mkDoctrine cells
  case validateDoctrine doc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  res <- case checkCoherence CP_All UseAllOriented 2 doc of
    Left err -> assertFailure (T.unpack err)
    Right r -> pure r
  assertBool "expected at least one failure" (any isFailure res)
  where
    isFailure r = case orWitness r of
      Nothing -> True
      Just _ -> False
