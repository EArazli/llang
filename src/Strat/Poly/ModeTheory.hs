{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.ModeTheory
  ( ModeName(..)
  , ModName(..)
  , ModExpr(..)
  , ModDecl(..)
  , ModeTheory(..)
  , emptyModeTheory
  , addMode
  , addModDecl
  , composeMod
  , checkWellFormed
  ) where

import Data.Text (Text)
import Data.Set (Set)
import Data.Map.Strict (Map)
import qualified Data.Set as S
import qualified Data.Map.Strict as M


newtype ModeName = ModeName Text deriving (Eq, Ord, Show)
newtype ModName = ModName Text deriving (Eq, Ord, Show)


data ModDecl = ModDecl
  { mdName :: ModName
  , mdSrc :: ModeName
  , mdTgt :: ModeName
  }
  deriving (Eq, Show)

-- Keep it extremely simple for now: a modality expression is a path of generators.
data ModExpr = ModExpr
  { meSrc :: ModeName
  , meTgt :: ModeName
  , mePath :: [ModName]
  }
  deriving (Eq, Ord, Show)


data ModeTheory = ModeTheory
  { mtModes :: Set ModeName
  , mtDecls :: Map ModName ModDecl
  , mtEqns :: [(ModExpr, ModExpr)]
  }
  deriving (Eq, Show)


emptyModeTheory :: ModeTheory
emptyModeTheory = ModeTheory S.empty M.empty []

addMode :: ModeName -> ModeTheory -> Either Text ModeTheory
addMode name mt
  | S.member name (mtModes mt) = Left "duplicate mode name"
  | otherwise = Right mt { mtModes = S.insert name (mtModes mt) }

addModDecl :: ModDecl -> ModeTheory -> Either Text ModeTheory
addModDecl decl mt
  | M.member (mdName decl) (mtDecls mt) = Left "duplicate modality name"
  | otherwise = Right mt { mtDecls = M.insert (mdName decl) decl (mtDecls mt) }

composeMod :: ModeTheory -> ModExpr -> ModExpr -> Either Text ModExpr
composeMod _ f g
  | meTgt f /= meSrc g = Left "mode mismatch in modality composition"
  | otherwise = Right ModExpr
      { meSrc = meSrc f
      , meTgt = meTgt g
      , mePath = mePath f <> mePath g
      }

checkWellFormed :: ModeTheory -> Either Text ()
checkWellFormed mt =
  mapM_ checkDecl (M.elems (mtDecls mt))
  where
    checkDecl decl
      | mdSrc decl `S.member` mtModes mt && mdTgt decl `S.member` mtModes mt = Right ()
      | otherwise = Left "modality declaration uses unknown mode"
