module Strat.Poly.TypeExpr
  ( TyVar(..)
  , TypeName(..)
  , TypeRef(..)
  , TypeExpr(..)
  , Context
  , typeMode
  ) where

import Data.Text (Text)
import Strat.Poly.ModeTheory (ModeName)


newtype TypeName = TypeName Text deriving (Eq, Ord, Show)

data TypeRef = TypeRef
  { trMode :: ModeName
  , trName :: TypeName
  } deriving (Eq, Ord, Show)

data TyVar = TyVar
  { tvName :: Text
  , tvMode :: ModeName
  } deriving (Eq, Ord, Show)

data TypeExpr
  = TVar TyVar
  | TCon TypeRef [TypeExpr]
  deriving (Eq, Ord, Show)

type Context = [TypeExpr]

typeMode :: TypeExpr -> ModeName
typeMode ty =
  case ty of
    TVar v -> tvMode v
    TCon r _ -> trMode r
