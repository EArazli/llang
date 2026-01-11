{-# LANGUAGE TypeFamilies #-}
module Strat.Meta.Term.FO where

import Strat.Meta.Term.Class
import Strat.Meta.Term.Syms
import Strat.Meta.Types
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Text (Text)

newtype Sym = Sym Text
  deriving (Eq, Ord, Show)

data V = V
  { vNs    :: Ns
  , vLocal :: Int
  }
  deriving (Eq, Ord, Show)

data Term
  = TVar V
  | TApp Sym [Term]
  deriving (Eq, Ord, Show)

instance TermLike Term where
  type Var Term = V

  isVar (TVar _) = True
  isVar _        = False

  asVar (TVar v) = Just v
  asVar _        = Nothing

  positions t = go [] t
    where
      go p (TVar _)    = [p]
      go p (TApp _ as) = p : concat [ go (p ++ [i]) a | (i, a) <- zip [0 ..] as ]

  subtermAt tm pos =
    case (tm, pos) of
      (_, []) -> Just tm
      (TApp _ as, i : rest) ->
        if i < 0 || i >= length as
          then Nothing
          else subtermAt (as !! i) rest
      _ -> Nothing

  replaceAt tm pos newTerm =
    case (tm, pos) of
      (_, []) -> Just newTerm
      (TApp f as, i : rest) ->
        if i < 0 || i >= length as
          then Nothing
          else do
            replaced <- replaceAt (as !! i) rest newTerm
            let as' = take i as ++ [replaced] ++ drop (i + 1) as
            pure (TApp f as')
      _ -> Nothing

  vars (TVar v)    = S.singleton v
  vars (TApp _ as) = S.unions (map vars as)

  applySubst (Subst s) tm =
    case tm of
      TVar v ->
        case M.lookup v s of
          Nothing -> tm
          Just t  -> applySubst (Subst s) t
      TApp f as -> TApp f (map (applySubst (Subst s)) as)

  renameVars f tm =
    case tm of
      TVar v     -> TVar (f v)
      TApp h as  -> TApp h (map (renameVars f) as)

instance ScopedVar V where
  setNs ns v = v { vNs = ns }

instance SymRenamable Term where
  renameSyms _ (TVar v) = TVar v
  renameSyms f (TApp (Sym s) args) = TApp (Sym (f s)) (map (renameSyms f) args)

  syms (TVar _) = S.empty
  syms (TApp (Sym s) args) = S.insert s (S.unions (map syms args))

instance Matchable Term where
  match pat target = Subst <$> go M.empty pat target
    where
      go subst p t =
        case p of
          TVar v ->
            case M.lookup v subst of
              Nothing -> Just (M.insert v t subst)
              Just t' ->
                if t' == t
                  then Just subst
                  else Nothing
          TApp f ps ->
            case t of
              TApp g ts
                | f == g && length ps == length ts ->
                    foldl step (Just subst) (zip ps ts)
                | otherwise -> Nothing
              _ -> Nothing

      step acc (p', t') = acc >>= \s -> go s p' t'

instance Unifiable Term where
  unify t1 t2 = Subst <$> go [(t1, t2)] M.empty
    where
      go [] subst = Just subst
      go ((s, t) : rest) subst = do
        let s' = applySubst (Subst subst) s
        let t' = applySubst (Subst subst) t
        if s' == t'
          then go rest subst
          else case (asVar s', asVar t') of
            (Just v, _) -> bind v t' rest subst
            (_, Just v) -> bind v s' rest subst
            _ ->
              case (s', t') of
                (TApp f as, TApp g bs)
                  | f == g && length as == length bs ->
                      go (zip as bs ++ rest) subst
                  | otherwise -> Nothing
                _ -> Nothing

      bind v term rest subst =
        if v `S.member` vars term
          then Nothing
          else go rest (M.insert v term subst)
