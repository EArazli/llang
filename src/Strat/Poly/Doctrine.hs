{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Doctrine
  ( StructuralLib(..)
  , Doctrine2(..)
  , cartMode
  ) where

import Data.Text (Text)
import Data.Map.Strict (Map)
import Strat.Kernel.Signature (Signature)
import Strat.Poly.Cell2 (Cell2)
import Strat.Poly.ModeTheory (ModeTheory, ModeName(..))


data StructuralLib
  = StructPlanar
  | StructSymmetric
  | StructCartesian
  deriving (Eq, Ord, Show)

cartMode :: ModeName
cartMode = ModeName "Cart"


data Doctrine2 = Doctrine2
  { d2Name :: Text
  , d2ModeTheory :: ModeTheory
  , d2Sig :: Signature
  , d2StructByMode :: Map ModeName StructuralLib
  , d2Cells2 :: [Cell2]
  }
  deriving (Eq, Show)
