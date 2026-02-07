{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.Helpers
  ( mkModes
  , mkModesFromSet
  , identityModeMap
  , identityModMap
  ) where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.Doctrine (Doctrine(..))
import Strat.Poly.ModeTheory


mkModes :: [ModeName] -> ModeTheory
mkModes modes =
  ModeTheory
    { mtModes = M.fromList [ (m, ModeInfo { miName = m, miDiscipline = Linear }) | m <- modes ]
    , mtDecls = M.empty
    , mtEqns = []
    , mtAdjs = []
    }

mkModesFromSet :: S.Set ModeName -> ModeTheory
mkModesFromSet = mkModes . S.toList

identityModeMap :: Doctrine -> M.Map ModeName ModeName
identityModeMap doc =
  M.fromList [ (m, m) | m <- M.keys (mtModes (dModes doc)) ]

identityModMap :: Doctrine -> M.Map ModName ModExpr
identityModMap doc =
  M.fromList
    [ (name, ModExpr { meSrc = mdSrc decl, meTgt = mdTgt decl, mePath = [name] })
    | (name, decl) <- M.toList (mtDecls (dModes doc))
    ]
