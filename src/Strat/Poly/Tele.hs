module Strat.Poly.Tele
  ( GenParam(..)
  , teleTyVars
  , teleTmVars
  ) where

import Strat.Poly.Syntax (TmVar)

data GenParam
  = GP_Ty TmVar
  | GP_Tm TmVar
  deriving (Eq, Ord, Read, Show)

teleTyVars :: [GenParam] -> [TmVar]
teleTyVars ps = [v | GP_Ty v <- ps]

teleTmVars :: [GenParam] -> [TmVar]
teleTmVars ps = [v | GP_Tm v <- ps]
