module Strat.Kernel.Unify
  ( match
  , unify
  ) where

import Strat.Kernel.Subst
import Strat.Kernel.Syntax
import qualified Data.Map.Strict as M
import qualified Data.Set as S

match :: Term -> Term -> Maybe Subst
match pat target = matchTerm M.empty pat target

unify :: Term -> Term -> Maybe Subst
unify t1 t2 = unifyTerm M.empty t1 t2

matchTerm :: Subst -> Term -> Term -> Maybe Subst
matchTerm subst pat target = do
  let p = applySubstTerm subst pat
  subst1 <- matchSort subst (termSort p) (termSort target)
  case termNode p of
    TVar v ->
      case M.lookup v subst1 of
        Nothing -> Just (M.insert v target subst1)
        Just t' ->
          if applySubstTerm subst1 t' == target
            then Just subst1
            else Nothing
    TOp op args ->
      case termNode target of
        TOp op' args'
          | op == op' && length args == length args' ->
              foldl step (Just subst1) (zip args args')
          | otherwise -> Nothing
        _ -> Nothing
  where
    step acc (a, b) = acc >>= \s -> matchTerm s a b

matchSort :: Subst -> Sort -> Sort -> Maybe Subst
matchSort subst s1 s2 = do
  let s1' = applySubstSort subst s1
  case (s1', s2) of
    (Sort n1 args1, Sort n2 args2)
      | n1 == n2 && length args1 == length args2 ->
          foldl step (Just subst) (zip args1 args2)
      | otherwise -> Nothing
  where
    step acc (a, b) = acc >>= \s -> matchTerm s a b

unifyTerm :: Subst -> Term -> Term -> Maybe Subst
unifyTerm subst t1 t2 = do
  let t1' = applySubstTerm subst t1
  let t2' = applySubstTerm subst t2
  if t1' == t2'
    then Just subst
    else do
      subst1 <- unifySort subst (termSort t1') (termSort t2')
      let u1 = applySubstTerm subst1 t1'
      let u2 = applySubstTerm subst1 t2'
      case (termNode u1, termNode u2) of
        (TVar v, _) -> bindVar subst1 v u2
        (_, TVar v) -> bindVar subst1 v u1
        (TOp op1 args1, TOp op2 args2)
          | op1 == op2 && length args1 == length args2 ->
              foldl step (Just subst1) (zip args1 args2)
          | otherwise -> Nothing
  where
    step acc (a, b) = acc >>= \s -> unifyTerm s a b

unifySort :: Subst -> Sort -> Sort -> Maybe Subst
unifySort subst s1 s2 =
  case (applySubstSort subst s1, applySubstSort subst s2) of
    (Sort n1 args1, Sort n2 args2)
      | n1 == n2 && length args1 == length args2 ->
          foldl step (Just subst) (zip args1 args2)
      | otherwise -> Nothing
  where
    step acc (a, b) = acc >>= \s -> unifyTerm s a b

bindVar :: Subst -> Var -> Term -> Maybe Subst
bindVar subst v term =
  let term' = applySubstTerm subst term
  in if v `S.member` varsTerm term'
       then Nothing
       else Just (M.insert v term' subst)

varsTerm :: Term -> S.Set Var
varsTerm term =
  varsInTerm term `S.union` varsInSort (termSort term)
  where
    varsInTerm t =
      case termNode t of
        TVar v -> S.singleton v
        TOp _ args -> S.unions (map varsTerm args)

varsInSort :: Sort -> S.Set Var
varsInSort (Sort _ idx) = S.unions (map varsTerm idx)
