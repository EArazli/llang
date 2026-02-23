{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.ModeSyntax
  ( ModeName(..)
  , ModName(..)
  , ModTransformName(..)
  , ModExpr(..)
  , ModDecl(..)
  , ModEqn(..)
  , ModTransformDecl(..)
  ) where

import Data.Text (Text)
import Strat.Poly.Names (GenName)


newtype ModeName = ModeName Text deriving (Eq, Ord, Show)
newtype ModName = ModName Text deriving (Eq, Ord, Show)
newtype ModTransformName = ModTransformName Text deriving (Eq, Ord, Show)

-- A modality expression is a composition path in application order.
data ModExpr = ModExpr
  { meSrc :: ModeName
  , meTgt :: ModeName
  , mePath :: [ModName]
  }
  deriving (Eq, Ord, Show)

data ModDecl = ModDecl
  { mdName :: ModName
  , mdSrc :: ModeName
  , mdTgt :: ModeName
  }
  deriving (Eq, Show)

data ModEqn = ModEqn
  { meLHS :: ModExpr
  , meRHS :: ModExpr
  } deriving (Eq, Show)

data ModTransformDecl = ModTransformDecl
  { mtdName :: ModTransformName
  , mtdFrom :: ModExpr
  , mtdTo :: ModExpr
  , mtdWitness :: GenName
  } deriving (Eq, Show)
