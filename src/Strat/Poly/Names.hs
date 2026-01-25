module Strat.Poly.Names
  ( GenName(..)
  ) where

import Data.Text (Text)

newtype GenName = GenName Text deriving (Eq, Ord, Show)
