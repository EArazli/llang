{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.UnifyTy
  ( Subst
  , unifyTy
  , unifyTyFlex
  , unifyCtx
  , unifyCtxFlex
  , applySubstTy
  , applySubstCtx
  , normalizeSubst
  , composeSubst
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.TypeExpr
import Strat.Poly.ModeTheory (ModeName(..), ModName(..), ModExpr(..), ModeTheory)


type Subst = M.Map TyVar TypeExpr

unifyTy :: ModeTheory -> TypeExpr -> TypeExpr -> Either Text Subst
unifyTy mt t1 t2 = unifyWith mt M.empty t1 t2

unifyTyFlex :: ModeTheory -> S.Set TyVar -> TypeExpr -> TypeExpr -> Either Text Subst
unifyTyFlex mt flex t1 t2 = unifyWithFlex mt flex M.empty t1 t2

unifyCtx :: ModeTheory -> Context -> Context -> Either Text Subst
unifyCtx mt ctx1 ctx2
  | length ctx1 /= length ctx2 = Left "unifyCtx: length mismatch"
  | otherwise = foldl step (Right M.empty) (zip ctx1 ctx2)
  where
    step acc (a, b) = do
      s <- acc
      s' <- unifyWith mt s a b
      pure (composeSubst mt s' s)

unifyCtxFlex :: ModeTheory -> S.Set TyVar -> Context -> Context -> Either Text Subst
unifyCtxFlex mt flex ctx1 ctx2
  | length ctx1 /= length ctx2 = Left "unifyCtxFlex: length mismatch"
  | otherwise = foldl step (Right M.empty) (zip ctx1 ctx2)
  where
    step acc (a, b) = do
      s <- acc
      let a' = applySubstTy mt s a
      let b' = applySubstTy mt s b
      s' <- unifyTyFlex mt flex a' b'
      pure (composeSubst mt s' s)

unifyWithFlex :: ModeTheory -> S.Set TyVar -> Subst -> TypeExpr -> TypeExpr -> Either Text Subst
unifyWithFlex mt flex subst t1 t2 =
  case (applySubstTy mt subst t1, applySubstTy mt subst t2) of
    (TVar v, t) ->
      unifyVar mt flex subst v t
    (t, TVar v) ->
      unifyVar mt flex subst v t
    (TCon n as, TCon m bs)
      | n == m && length as == length bs ->
          foldl step (Right subst) (zip as bs)
      | otherwise ->
          Left ("unifyTyFlex: cannot unify " <> renderTy (TCon n as) <> " with " <> renderTy (TCon m bs))
    (TMod me1 x1, TMod me2 x2)
      | me1 == me2 ->
          unifyWithFlex mt flex subst x1 x2
      | otherwise ->
          Left ("unifyTyFlex: cannot unify " <> renderTy (TMod me1 x1) <> " with " <> renderTy (TMod me2 x2))
    (ta, tb) ->
      Left ("unifyTyFlex: cannot unify " <> renderTy ta <> " with " <> renderTy tb)
  where
    step acc (a, b) = do
      s <- acc
      s' <- unifyWithFlex mt flex s a b
      pure (composeSubst mt s' s)

unifyVar :: ModeTheory -> S.Set TyVar -> Subst -> TyVar -> TypeExpr -> Either Text Subst
unifyVar mt flex subst v t
  | v `S.member` flex =
      bindVar mt subst v t
  | otherwise =
      case t of
        TVar v' | v' == v -> Right subst
        TVar v' | v' `S.member` flex -> bindVar mt subst v' (TVar v)
        _ -> Left ("unifyTyFlex: rigid variable mismatch " <> renderVar v <> " with " <> renderTy t)

unifyWith :: ModeTheory -> Subst -> TypeExpr -> TypeExpr -> Either Text Subst
unifyWith mt subst t1 t2 =
  case (applySubstTy mt subst t1, applySubstTy mt subst t2) of
    (TVar v, t) -> bindVar mt subst v t
    (t, TVar v) -> bindVar mt subst v t
    (TCon n as, TCon m bs)
      | n == m && length as == length bs ->
          foldl step (Right subst) (zip as bs)
      | otherwise ->
          Left ("unifyTy: cannot unify " <> renderTy (TCon n as) <> " with " <> renderTy (TCon m bs))
    (TMod me1 x1, TMod me2 x2)
      | me1 == me2 -> unifyWith mt subst x1 x2
      | otherwise -> Left ("unifyTy: cannot unify " <> renderTy (TMod me1 x1) <> " with " <> renderTy (TMod me2 x2))
    (ta, tb) ->
      Left ("unifyTy: cannot unify " <> renderTy ta <> " with " <> renderTy tb)
  where
    step acc (a, b) = do
      s <- acc
      s' <- unifyWith mt s a b
      pure (composeSubst mt s' s)

bindVar :: ModeTheory -> Subst -> TyVar -> TypeExpr -> Either Text Subst
bindVar mt subst v t
  | tvMode v /= typeMode t = Left ("unifyTy: mode mismatch " <> renderVar v <> " with " <> renderTy t)
  | t' == TVar v = Right subst
  | occurs v t' = Left ("unifyTy: occurs check failed for " <> renderVar v <> " in " <> renderTy t')
  | otherwise =
      let subst' = M.insert v t' (M.map (applySubstTy mt (M.singleton v t')) subst)
       in Right (normalizeSubst mt subst')
  where
    t' = applySubstTy mt subst t

occurs :: TyVar -> TypeExpr -> Bool
occurs v t =
  case t of
    TVar v' -> v == v'
    TCon _ args -> any (occurs v) args
    TMod _ inner -> occurs v inner

applySubstTy :: ModeTheory -> Subst -> TypeExpr -> TypeExpr
applySubstTy mt subst ty =
  let raw = go S.empty ty
   in case normalizeTypeExpr mt raw of
        Right out -> out
        Left _ -> raw
  where
    go seen expr =
      case expr of
        TVar v ->
          case M.lookup v subst of
            Nothing -> TVar v
            Just t ->
              if v `S.member` seen
                then TVar v
                else go (S.insert v seen) t
        TCon n args -> TCon n (map (go seen) args)
        TMod me inner -> TMod me (go seen inner)

applySubstCtx :: ModeTheory -> Subst -> Context -> Context
applySubstCtx mt subst = map (applySubstTy mt subst)

normalizeSubst :: ModeTheory -> Subst -> Subst
normalizeSubst mt subst =
  M.fromList
    [ (v, t')
    | (v, t) <- M.toList subst
    , let t' = applySubstTy mt subst t
    , t' /= TVar v
    ]

composeSubst :: ModeTheory -> Subst -> Subst -> Subst
composeSubst mt s2 s1 =
  let s1' = M.map (applySubstTy mt s2) s1
   in normalizeSubst mt (M.union s1' s2)

renderTy :: TypeExpr -> Text
renderTy ty =
  case ty of
    TVar v -> renderVar v
    TCon ref [] -> renderTypeRef ref
    TCon ref args ->
      renderTypeRef ref <> "(" <> T.intercalate ", " (map renderTy args) <> ")"
    TMod me inner -> renderModExpr me <> "(" <> renderTy inner <> ")"

renderVar :: TyVar -> Text
renderVar v = tvName v <> "@" <> renderMode (tvMode v)

renderTypeRef :: TypeRef -> Text
renderTypeRef ref =
  renderMode (trMode ref) <> "." <> renderTypeName (trName ref)

renderTypeName :: TypeName -> Text
renderTypeName (TypeName n) = n

renderMode :: ModeName -> Text
renderMode (ModeName n) = n

renderModExpr :: ModExpr -> Text
renderModExpr me =
  case reverse (mePath me) of
    [] -> "id@" <> renderMode (meSrc me)
    names -> T.intercalate "." (map renderModName names)

renderModName :: ModName -> Text
renderModName (ModName n) = n
