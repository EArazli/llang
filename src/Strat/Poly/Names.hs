module Strat.Poly.Names
  ( GenName(..)
  , BoxName(..)
  ) where

import Data.Text (Text)

newtype GenName = GenName Text deriving (Eq, Ord, Show)
newtype BoxName = BoxName Text deriving (Eq, Ord, Show)
