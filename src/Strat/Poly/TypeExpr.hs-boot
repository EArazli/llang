module Strat.Poly.TypeExpr where

import Data.Text (Text)
import qualified Data.Set as S
import Strat.Poly.ModeTheory (ModeName)

data TypeExpr
data TyVar
type Context = [TypeExpr]

instance Eq TypeExpr
instance Ord TypeExpr
instance Show TypeExpr

instance Eq TyVar
instance Ord TyVar
instance Show TyVar

data TmVar = TmVar
  { tmvName :: Text
  , tmvSort :: TypeExpr
  , tmvScope :: Int
  }

instance Eq TmVar
instance Ord TmVar
instance Show TmVar

boundTmIndicesType :: TypeExpr -> S.Set Int
typeMode :: TypeExpr -> ModeName
