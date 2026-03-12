{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.GenArgs
  ( Fresh
  , evalFresh
  , freshInt
  , liftEither
  , bindCodeArg
  , freshGenParams
  , freshGenParamsFresh
  , elabGenArgsSequential
  , elabGenArgsSequentialWith
  ) where

import Control.Monad (foldM)
import qualified Data.Map.Strict as M
import Data.Text (Text)
import qualified Data.Text as T
import Strat.Poly.DSL.AST (RawPolyObjExpr)
import Strat.Poly.DSL.Elab.Term (elabObjExprWithTables, elabTmTermWithTables)
import Strat.Poly.DefEq (termExprToDiagramChecked)
import Strat.Poly.Doctrine (CtorTables, Doctrine)
import Strat.Poly.Obj
  ( CodeArg(..)
  , Obj(..)
  , TermDiagram
  , TmVar(..)
  , defaultMetaArgs
  , modeCtxGlobals
  , objMode
  , tmVarOwner
  )
import Strat.Poly.Tele (GenParam(..))
import Strat.Poly.TermExpr (TermExpr(..))
import Strat.Poly.TypeTheory (TypeTheory)
import Strat.Poly.UnifyObj (Subst, applySubstObj, composeSubst, emptySubst, mkSubst)

newtype Fresh a = Fresh (Int -> Either Text (a, Int))

instance Functor Fresh where
  fmap f (Fresh g) =
    Fresh (\n -> do
      (a, n') <- g n
      pure (f a, n'))

instance Applicative Fresh where
  pure a = Fresh (\n -> Right (a, n))
  Fresh f <*> Fresh g =
    Fresh (\n -> do
      (h, n1) <- f n
      (a, n2) <- g n1
      pure (h a, n2))

instance Monad Fresh where
  Fresh g >>= k =
    Fresh (\n -> do
      (a, n1) <- g n
      let Fresh h = k a
      h n1)

evalFresh :: Fresh a -> Either Text a
evalFresh (Fresh f) = fmap fst (f 0)

freshInt :: Fresh Int
freshInt = Fresh (\n -> Right (n, n + 1))

liftEither :: Either Text a -> Fresh a
liftEither (Left err) = Fresh (\_ -> Left err)
liftEither (Right a) = pure a

bindCodeArg :: TypeTheory -> TmVar -> CodeArg -> Subst -> Either Text Subst
bindCodeArg tt v arg subst = do
  singleton <- mkSubst [(v, arg)]
  composeSubst tt singleton subst

freshGenParams :: TypeTheory -> [Obj] -> [GenParam] -> Either Text ([GenParam], Subst)
freshGenParams tt tmCtx =
  evalFresh . freshGenParamsFresh tt tmCtx

freshGenParamsFresh :: TypeTheory -> [Obj] -> [GenParam] -> Fresh ([GenParam], Subst)
freshGenParamsFresh tt tmCtx = go emptySubst []
  where
    go subst acc [] =
      pure (reverse acc, subst)
    go subst acc (param : rest) =
      case param of
        GP_Ty v -> do
          fresh <- freshTyParam v
          subst' <- liftEither (bindCodeArg tt v (CAObj (OVar fresh)) subst)
          go subst' (GP_Ty fresh : acc) rest
        GP_Tm v -> do
          sort' <- liftEither (applySubstObj tt subst (tmvSort v))
          (fresh, tm) <- freshTmParam tt tmCtx v sort'
          subst' <- liftEither (bindCodeArg tt v (CATm tm) subst)
          go subst' (GP_Tm fresh : acc) rest

elabGenArgsSequential
  :: Doctrine
  -> CtorTables
  -> TypeTheory
  -> [Obj]
  -> [TmVar]
  -> [TmVar]
  -> [GenParam]
  -> [RawPolyObjExpr]
  -> Either Text ([CodeArg], Subst)
elabGenArgsSequential doc ctorTables tt tmCtx tyVars tmVars =
  elabGenArgsSequentialWith
    tt
    (\v raw -> do
      let ownerMode = tmVarOwner v
      ty <- elabObjExprWithTables doc ctorTables tyVars tmVars M.empty ownerMode raw
      if tmVarOwner v == tmVarOwner v && objMode ty == ownerMode
        then Right ty
        else Left "generator type argument mode mismatch"
    )
    (\expectedSort _v raw -> elabTmTermWithTables doc ctorTables tyVars tmVars M.empty (Just expectedSort) raw)

elabGenArgsSequentialWith
  :: TypeTheory
  -> (TmVar -> a -> Either Text Obj)
  -> (Obj -> TmVar -> a -> Either Text TermDiagram)
  -> [GenParam]
  -> [a]
  -> Either Text ([CodeArg], Subst)
elabGenArgsSequentialWith tt elabTyArg elabTmArg params args
  | length params /= length args =
      Left "generator argument mismatch"
  | otherwise =
      do
        (argsRev, subst) <- foldM step ([], emptySubst) (zip params args)
        pure (reverse argsRev, subst)
  where
    step (acc, substAcc) (param, rawArg) =
      case param of
        GP_Ty v -> do
          ty <- elabTyArg v rawArg
          subst' <- bindCodeArg tt v (CAObj ty) substAcc
          pure (CAObj ty : acc, subst')
        GP_Tm v -> do
          expectedSort <- applySubstObj tt substAcc (tmvSort v)
          tm <- elabTmArg expectedSort v rawArg
          subst' <- bindCodeArg tt v (CATm tm) substAcc
          pure (CATm tm : acc, subst')

freshTyParam :: TmVar -> Fresh TmVar
freshTyParam v = do
  n <- freshInt
  let name = tmvName v <> T.pack ("#" <> show n)
  pure v { tmvName = name }

freshTmParam :: TypeTheory -> [Obj] -> TmVar -> Obj -> Fresh (TmVar, TermDiagram)
freshTmParam tt tmCtx v sortTy = do
  n <- freshInt
  let name = tmvName v <> T.pack ("#" <> show n)
  let fresh =
        TmVar
          { tmvName = name
          , tmvSort = sortTy
          , tmvScope = max (tmvScope v) (length (modeCtxGlobals tmCtx (objMode sortTy)))
          , tmvOwnerMode = Nothing
          }
  tm <- liftEither (termExprToDiagramChecked tt tmCtx sortTy (TMMeta fresh (defaultMetaArgs tmCtx fresh)))
  pure (fresh, tm)
