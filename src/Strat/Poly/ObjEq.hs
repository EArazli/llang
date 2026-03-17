module Strat.Poly.ObjEq
  ( ObjEqInCtx
  ) where

import Data.Text (Text)
import Strat.Poly.Obj (Obj)

type ObjEqInCtx = [Obj] -> Obj -> Obj -> Either Text Bool
