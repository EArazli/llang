module Strat.Poly.TypeExpr
  ( TyVar(..)
  , TypeName(..)
  , TypeExpr(..)
  , Context
  ) where

import Data.Text (Text)


newtype TyVar = TyVar Text deriving (Eq, Ord, Show)
newtype TypeName = TypeName Text deriving (Eq, Ord, Show)

data TypeExpr
  = TVar TyVar
  | TCon TypeName [TypeExpr]
  deriving (Eq, Ord, Show)

type Context = [TypeExpr]
