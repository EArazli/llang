{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.STLCSurface
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import Data.Text (Text)
import qualified Data.Text as T
import Paths_llang (getDataFileName)
import Strat.Frontend.Loader (loadModule)
import Strat.Frontend.Env (meDoctrines, meSurfaces)
import Strat.Poly.Doctrine (Doctrine)
import Strat.Poly.Surface (PolySurfaceDef)
import Strat.Poly.Surface.Elab (elabSurfaceExpr)
import Strat.Poly.Graph (Diagram(..), Edge(..), EdgePayload(..))
import Strat.Poly.Names (GenName(..))


tests :: TestTree
tests =
  testGroup
    "Poly.STLCSurface"
    [ testCase "lam2 weakens outer var" testLam2Weakening
    ]

testLam2Weakening :: Assertion
testLam2Weakening = do
  (doc, surf) <- loadSTLCSurface
  case elabSurfaceExpr doc surf "lam x:Bool. lam y:Bool. x" of
    Left err -> assertFailure (T.unpack err)
    Right diag -> do
      assertHasGen "exl" diag
      assertHasGen "comp" diag

loadSTLCSurface :: IO (Doctrine, PolySurfaceDef)
loadSTLCSurface = do
  path <- getDataFileName "examples/ccc_surface/stlc.surface.llang"
  envResult <- loadModule path
  env <- case envResult of
    Left err -> assertFailure (T.unpack err)
    Right env -> pure env
  doc <- case M.lookup "CCC" (meDoctrines env) of
    Nothing -> assertFailure "doctrine CCC not found"
    Just d -> pure d
  surf <- case M.lookup "STLC" (meSurfaces env) of
    Nothing -> assertFailure "surface STLC not found"
    Just s -> pure s
  pure (doc, surf)

assertHasGen :: Text -> Diagram -> Assertion
assertHasGen name diag =
  let payloads = [ g | Edge _ (PGen g) _ _ <- IM.elems (dEdges diag) ]
  in if GenName name `elem` payloads
      then pure ()
      else assertFailure ("expected gen " <> T.unpack name)
