module Strat.Poly.RunSpec
  ( PolyRunSpec(..)
  ) where

import Data.Text (Text)
import Strat.Frontend.RunSpec (RunShow)
import Strat.Kernel.RewriteSystem (RewritePolicy)


data PolyRunSpec = PolyRunSpec
  { prName :: Text
  , prDoctrine :: Text
  , prMode :: Maybe Text
  , prSurface :: Maybe Text
  , prModel :: Maybe Text
  , prPolicy :: RewritePolicy
  , prFuel :: Int
  , prShowFlags :: [RunShow]
  , prExprText :: Text
  } deriving (Eq, Show)
