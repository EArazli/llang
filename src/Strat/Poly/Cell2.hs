module Strat.Poly.Cell2
  ( Cell2(..)
  ) where

import Data.Text (Text)
import Strat.Common.Rules (RuleClass, Orientation)
import Strat.Poly.TypeExpr (TyVar, TmVar)
import Strat.Poly.Diagram (Diagram)


data Cell2 = Cell2
  { c2Name :: Text
  , c2Class :: RuleClass
  , c2Orient :: Orientation
  , c2TyVars :: [TyVar]
  , c2TmVars :: [TmVar]
  , c2LHS :: Diagram
  , c2RHS :: Diagram
  }
  deriving (Eq, Show)
