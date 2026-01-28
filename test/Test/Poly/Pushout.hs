{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.Pushout
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Data.Text (Text)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.ModeTheory (ModeName(..), ModeTheory(..))
import Strat.Poly.TypeExpr (TyVar(..), TypeExpr(..))
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Diagram (genD, idD)
import Strat.Poly.Doctrine (Doctrine(..), GenDecl(..), validateDoctrine)
import Strat.Poly.Cell2 (Cell2(..))
import Strat.Poly.Morphism (Morphism(..))
import Strat.Poly.Pushout (computePolyPushout, PolyPushoutResult(..))
import Strat.Kernel.Types (RuleClass(..), Orientation(..))
import Strat.Kernel.RewriteSystem (RewritePolicy(..))


tests :: TestTree
tests =
  testGroup
    "Poly.Pushout"
    [ testCase "pushout dedups equations by body" testPushoutDedupByBody
    ]


testPushoutDedupByBody :: Assertion
testPushoutDedupByBody = do
  let mode = ModeName "M"
  base <- case mkDoctrine mode "Interface" (TyVar "a") "eqI" of
    Left err -> assertFailure err
    Right d -> pure d
  left <- case mkDoctrine mode "Left" (TyVar "a") "eqLeft" of
    Left err -> assertFailure err
    Right d -> pure d
  right <- case mkDoctrine mode "Right" (TyVar "b") "eqRight" of
    Left err -> assertFailure err
    Right d -> pure d
  let morLeft = mkInclusionMorph "Left.in" base left (TyVar "a")
  let morRight = mkInclusionMorph "Right.in" base right (TyVar "b")
  res <- case computePolyPushout "Po" morLeft morRight of
    Left err -> assertFailure (show err)
    Right r -> pure r
  length (dCells2 (poDoctrine res)) @?= 1


mkDoctrine :: ModeName -> Text -> TyVar -> Text -> Either String Doctrine
mkDoctrine mode name tyVar cellName = do
  let gen = GenDecl
        { gdName = GenName "f"
        , gdMode = mode
        , gdTyVars = [tyVar]
        , gdDom = [TVar tyVar]
        , gdCod = [TVar tyVar]
        }
  lhs <- case genD mode [TVar tyVar] [TVar tyVar] (gdName gen) of
    Left err -> Left (show err)
    Right d -> Right d
  let rhs = idD mode [TVar tyVar]
  let cell = Cell2
        { c2Name = cellName
        , c2Class = Computational
        , c2Orient = LR
        , c2TyVars = [tyVar]
        , c2LHS = lhs
        , c2RHS = rhs
        }
  let doc = Doctrine
        { dName = name
        , dModes = ModeTheory (S.singleton mode) M.empty []
        , dTypes = M.empty
        , dGens = M.fromList [(mode, M.fromList [(gdName gen, gen)])]
        , dCells2 = [cell]
        }
  case validateDoctrine doc of
    Left err -> Left (show err)
    Right () -> Right doc

mkInclusionMorph :: Text -> Doctrine -> Doctrine -> TyVar -> Morphism
mkInclusionMorph name src tgt tyVar =
  let mode = ModeName "M"
      diag = case genD mode [TVar tyVar] [TVar tyVar] (GenName "f") of
        Left _ -> error "mkInclusionMorph: genD failed"
        Right d -> d
      genMap = M.fromList [((mode, GenName "f"), diag)]
  in Morphism
      { morName = name
      , morSrc = src
      , morTgt = tgt
      , morTypeMap = M.empty
      , morGenMap = genMap
      , morPolicy = UseAllOriented
      , morFuel = 10
      }
