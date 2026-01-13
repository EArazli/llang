module Strat.Kernel.Subst where

import Strat.Kernel.Syntax
import qualified Data.Map.Strict as M
import qualified Data.Set as S

type Subst = M.Map Var Term

applySubstSort :: Subst -> Sort -> Sort
applySubstSort subst (Sort name idx) =
  Sort name (map (applySubstTerm subst) idx)

applySubstTerm :: Subst -> Term -> Term
applySubstTerm subst term = go S.empty term
  where
    go seen tm =
      case termNode tm of
        TVar v ->
          case M.lookup v subst of
            Nothing ->
              Term
                { termSort = applySubstSort subst (termSort tm)
                , termNode = TVar v
                }
            Just t ->
              if v `S.member` seen
                then Term
                  { termSort = applySubstSort subst (termSort tm)
                  , termNode = TVar v
                  }
                else go (S.insert v seen) t
        TOp op args ->
          let args' = map (go seen) args
          in Term
              { termSort = applySubstSort subst (termSort tm)
              , termNode = TOp op args'
              }
