module Strat.Poly.TypeTheory
  ( TypeTheory(..)
  , TypeParamSig(..)
  , defaultIxFuel
  , modeOnlyTypeTheory
  ) where

import qualified Data.Map.Strict as M
import Strat.Poly.IndexTheory (TypeTheory(..), TypeParamSig(..))
import Strat.Poly.ModeTheory (ModeTheory)


defaultIxFuel :: Int
defaultIxFuel = 200

modeOnlyTypeTheory :: ModeTheory -> TypeTheory
modeOnlyTypeTheory mt =
  TypeTheory
    { ttModes = mt
    , ttIndex = M.empty
    , ttTypeParams = M.empty
    , ttIxFuel = defaultIxFuel
    }
