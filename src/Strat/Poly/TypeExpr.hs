module Strat.Poly.TypeExpr
  ( TypeExpr(..)
  , Context
  , asSort
  ) where

import Data.Text (Text)
import Strat.Kernel.Syntax (Sort)


data TypeExpr
  = TySort Sort
  | TyCon Text [TypeExpr]
  deriving (Eq, Ord, Show)

type Context = [TypeExpr]

asSort :: TypeExpr -> Maybe Sort
asSort (TySort s) = Just s
asSort _ = Nothing
