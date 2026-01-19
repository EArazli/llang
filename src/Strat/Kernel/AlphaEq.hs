module Strat.Kernel.AlphaEq
  ( alphaEqSort
  , alphaEqSortCtor
  , alphaEqOpDecl
  , alphaEqEquation
  ) where

import Strat.Kernel.Rule (Equation(..))
import Strat.Kernel.Signature
import Strat.Kernel.Subst (applySubstSort, applySubstTerm)
import Strat.Kernel.Syntax
import Strat.Kernel.Term
import qualified Data.Map.Strict as M


alphaEqSort :: Sort -> Sort -> Bool
alphaEqSort = (==)

alphaEqSortCtor :: SortCtor -> SortCtor -> Bool
alphaEqSortCtor c1 c2 =
  let tele1 = scTele c1
      tele2 = scTele c2
  in length tele1 == length tele2
      && and (zipWith alphaEqBinder tele1 tele2)
  where
    subst =
      M.fromList
        [ (v2, mkVar s1 v1)
        | (Binder v1 s1, Binder v2 _) <- zip (scTele c1) (scTele c2)
        ]
    alphaEqBinder (Binder _ s1) (Binder _ s2) =
      let s2' = applySubstSort subst s2
      in s1 == s2'

alphaEqOpDecl :: OpDecl -> OpDecl -> Bool
alphaEqOpDecl d1 d2 =
  let tele1 = opTele d1
      tele2 = opTele d2
  in length tele1 == length tele2
      && and (zipWith alphaEqBinder tele1 tele2)
      && opResult d1 == applySubstSort subst (opResult d2)
  where
    subst =
      M.fromList
        [ (v2, mkVar s1 v1)
        | (Binder v1 s1, Binder v2 _) <- zip (opTele d1) (opTele d2)
        ]
    alphaEqBinder (Binder _ s1) (Binder _ s2) =
      let s2' = applySubstSort subst s2
      in s1 == s2'

alphaEqEquation :: Equation -> Equation -> Bool
alphaEqEquation e1 e2 =
  eqClass e1 == eqClass e2
    && eqOrient e1 == eqOrient e2
    && length tele1 == length tele2
    && and (zipWith alphaEqBinder tele1 tele2)
    && eqLHS e1 == applySubstTerm subst (eqLHS e2)
    && eqRHS e1 == applySubstTerm subst (eqRHS e2)
  where
    tele1 = eqTele e1
    tele2 = eqTele e2
    subst =
      M.fromList
        [ (v2, mkVar s1 v1)
        | (Binder v1 s1, Binder v2 _) <- zip tele1 tele2
        ]
    alphaEqBinder (Binder _ s1) (Binder _ s2) =
      let s2' = applySubstSort subst s2
      in s1 == s2'
