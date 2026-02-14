module Strat.Poly.UnifyTy where

import Data.Text (Text)
import qualified Data.Set as S
import {-# SOURCE #-} Strat.Poly.TypeExpr (TyVar, TmVar, TypeExpr, Context)
import {-# SOURCE #-} Strat.Poly.TypeTheory (TypeTheory)

data Subst
instance Eq Subst
instance Ord Subst
instance Show Subst

emptySubst :: Subst

unifyTyFlex
  :: TypeTheory
  -> [TypeExpr]
  -> S.Set TyVar
  -> S.Set TmVar
  -> Subst
  -> TypeExpr
  -> TypeExpr
  -> Either Text Subst

applySubstCtx :: TypeTheory -> Subst -> Context -> Either Text Context

unifyCtx
  :: TypeTheory
  -> [TypeExpr]
  -> S.Set TyVar
  -> S.Set TmVar
  -> Context
  -> Context
  -> Either Text Subst

applySubstTy :: TypeTheory -> Subst -> TypeExpr -> Either Text TypeExpr
