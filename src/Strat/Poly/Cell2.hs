module Strat.Poly.Cell2
  ( Cell2(..)
  , c2TyVars
  , c2TmVars
  ) where

import Data.Text (Text)
import Strat.Common.Rules (RuleClass, Orientation)
import Strat.Poly.Obj (TmVar)
import Strat.Poly.Syntax (Diagram)
import Strat.Poly.Tele (GenParam(..), teleTyVars, teleTmVars)


data Cell2 = Cell2
  { c2Name :: Text
  , c2Class :: RuleClass
  , c2Orient :: Orientation
  , c2Params :: [GenParam]
  , c2LHS :: Diagram
  , c2RHS :: Diagram
  }
  deriving (Eq, Read, Show)

c2TyVars :: Cell2 -> [TmVar]
c2TyVars
  =
  teleTyVars . c2Params

c2TmVars :: Cell2 -> [TmVar]
c2TmVars
  =
  teleTmVars . c2Params
