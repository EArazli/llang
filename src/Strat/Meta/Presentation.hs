module Strat.Meta.Presentation where

import Strat.Meta.Rule
import Data.Text (Text)

data Presentation t = Presentation
  { presName :: Text
  , presEqs  :: [Equation t]
  }
  deriving (Eq, Show)
