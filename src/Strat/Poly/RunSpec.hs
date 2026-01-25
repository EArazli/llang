module Strat.Poly.RunSpec
  ( PolyRunSpec(..)
  ) where

import Data.Text (Text)
import Strat.Frontend.RunSpec (RunShow)


data PolyRunSpec = PolyRunSpec
  { prName :: Text
  , prDoctrine :: Text
  , prFuel :: Int
  , prShowFlags :: [RunShow]
  , prExprText :: Text
  } deriving (Eq, Show)
