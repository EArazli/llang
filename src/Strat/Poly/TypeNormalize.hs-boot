module Strat.Poly.TypeNormalize where

import Data.Text (Text)
import Strat.Poly.TypeExpr (TypeExpr)
import Strat.Poly.TypeTheory (TypeTheory)

normalizeTypeDeepWithCtx :: TypeTheory -> [TypeExpr] -> TypeExpr -> Either Text TypeExpr
