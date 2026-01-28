{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Surface
  ( PolySurfaceKind(..)
  , PolySurfaceDef(..)
  , elabPolySurfaceDecl
  ) where

import Data.Text (Text)
import qualified Data.Set as S
import Strat.Poly.ModeTheory (ModeName(..), mtModes)
import Strat.Poly.Doctrine (dModes)
import Strat.Kernel.DSL.AST (RawPolySurfaceDecl(..))
import Strat.Poly.Doctrine (Doctrine)


data PolySurfaceKind
  = SurfaceSSA
  | SurfaceCartTerm
  | SurfaceSTLC
  deriving (Eq, Show)


data PolySurfaceDef = PolySurfaceDef
  { psName :: Text
  , psDoctrine :: Text
  , psMode :: ModeName
  , psKind :: PolySurfaceKind
  } deriving (Eq, Show)

elabPolySurfaceDecl :: Doctrine -> RawPolySurfaceDecl -> Either Text PolySurfaceDef
elabPolySurfaceDecl doc decl = do
  let mode = ModeName (rpsMode decl)
  if mode `S.member` mtModes (dModes doc)
    then Right PolySurfaceDef
      { psName = rpsName decl
      , psDoctrine = rpsDoctrine decl
      , psMode = mode
      , psKind = SurfaceSSA
      }
    else Left "polysurface: unknown mode"
