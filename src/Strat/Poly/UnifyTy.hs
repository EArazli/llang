{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.UnifyTy
  ( Subst
  , unifyTy
  , unifyCtx
  , applySubstTy
  , applySubstCtx
  , composeSubst
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import Strat.Poly.TypeExpr


type Subst = M.Map TyVar TypeExpr

unifyTy :: TypeExpr -> TypeExpr -> Either Text Subst
unifyTy t1 t2 = unifyWith M.empty t1 t2

unifyCtx :: Context -> Context -> Either Text Subst
unifyCtx ctx1 ctx2
  | length ctx1 /= length ctx2 = Left "unifyCtx: length mismatch"
  | otherwise = foldl step (Right M.empty) (zip ctx1 ctx2)
  where
    step acc (a, b) = do
      s <- acc
      s' <- unifyWith s a b
      pure (composeSubst s' s)

unifyWith :: Subst -> TypeExpr -> TypeExpr -> Either Text Subst
unifyWith subst t1 t2 =
  case (applySubstTy subst t1, applySubstTy subst t2) of
    (TVar v, t) -> bindVar subst v t
    (t, TVar v) -> bindVar subst v t
    (TCon n as, TCon m bs)
      | n == m && length as == length bs ->
          foldl step (Right subst) (zip as bs)
      | otherwise ->
          Left ("unifyTy: cannot unify " <> renderTy (TCon n as) <> " with " <> renderTy (TCon m bs))
    (ta, tb) ->
      Left ("unifyTy: cannot unify " <> renderTy ta <> " with " <> renderTy tb)
  where
    step acc (a, b) = do
      s <- acc
      s' <- unifyWith s a b
      pure (composeSubst s' s)

bindVar :: Subst -> TyVar -> TypeExpr -> Either Text Subst
bindVar subst v t
  | t == TVar v = Right subst
  | occurs v t = Left ("unifyTy: occurs check failed for " <> renderVar v <> " in " <> renderTy t)
  | otherwise =
      let subst' = M.insert v t (M.map (applySubstTy (M.singleton v t)) subst)
      in Right subst'

occurs :: TyVar -> TypeExpr -> Bool
occurs v t =
  case t of
    TVar v' -> v == v'
    TCon _ args -> any (occurs v) args

applySubstTy :: Subst -> TypeExpr -> TypeExpr
applySubstTy subst ty =
  case ty of
    TVar v ->
      case M.lookup v subst of
        Nothing -> TVar v
        Just t -> applySubstTy subst t
    TCon n args -> TCon n (map (applySubstTy subst) args)

applySubstCtx :: Subst -> Context -> Context
applySubstCtx subst = map (applySubstTy subst)

composeSubst :: Subst -> Subst -> Subst
composeSubst s2 s1 =
  let s1' = M.map (applySubstTy s2) s1
  in M.union s1' s2

renderTy :: TypeExpr -> Text
renderTy = T.pack . show

renderVar :: TyVar -> Text
renderVar = T.pack . show
