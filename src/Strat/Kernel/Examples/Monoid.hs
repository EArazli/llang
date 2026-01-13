{-# LANGUAGE OverloadedStrings #-}
module Strat.Kernel.Examples.Monoid
  ( objSortName
  , objSort
  , eName
  , mName
  , sigMonoid
  , eTerm
  , mTerm
  , eqUnitL
  , eqAssoc
  , presMonoid
  ) where

import Strat.Kernel.Signature
import Strat.Kernel.Syntax
import Strat.Kernel.Term
import Strat.Kernel.Rule
import Strat.Kernel.Presentation
import Strat.Kernel.Types
import qualified Data.Map.Strict as M

objSortName :: SortName
objSortName = SortName "Obj"

objSort :: Sort
objSort = Sort objSortName []

eName :: OpName
eName = OpName "e"

mName :: OpName
mName = OpName "m"

sigMonoid :: Signature
sigMonoid =
  Signature
    { sigSortCtors = M.fromList [(objSortName, SortCtor objSortName [])]
    , sigOps = M.fromList [(eName, eDecl), (mName, mDecl)]
    }
  where
    eDecl = OpDecl eName [] objSort
    mDecl =
      let scope = ScopeId "op:m"
          a = Var scope 0
          b = Var scope 1
      in OpDecl mName [Binder a objSort, Binder b objSort] objSort

eTerm :: Either TypeError Term
eTerm = mkOp sigMonoid eName []

mTerm :: Term -> Term -> Either TypeError Term
mTerm a b = mkOp sigMonoid mName [a, b]

unsafeOp :: Either TypeError Term -> Term
unsafeOp tm =
  case tm of
    Left err -> error (show err)
    Right t -> t

eqUnitL :: Equation
eqUnitL =
  let scope = ScopeId "eq:unitL"
      vx = Var scope 0
      x = mkVar objSort vx
      lhsTerm = unsafeOp (mTerm (unsafeOp eTerm) x)
      rhsTerm = x
  in Equation
      { eqName = "unitL"
      , eqClass = Computational
      , eqOrient = LR
      , eqTele = [Binder vx objSort]
      , eqLHS = lhsTerm
      , eqRHS = rhsTerm
      }

eqAssoc :: Equation
eqAssoc =
  let scope = ScopeId "eq:assoc"
      vx = Var scope 0
      vy = Var scope 1
      vz = Var scope 2
      x = mkVar objSort vx
      y = mkVar objSort vy
      z = mkVar objSort vz
      lhsTerm = unsafeOp (mTerm (unsafeOp (mTerm x y)) z)
      rhsTerm = unsafeOp (mTerm x (unsafeOp (mTerm y z)))
  in Equation
      { eqName = "assoc"
      , eqClass = Computational
      , eqOrient = LR
      , eqTele = [Binder vx objSort, Binder vy objSort, Binder vz objSort]
      , eqLHS = lhsTerm
      , eqRHS = rhsTerm
      }

presMonoid :: Presentation
presMonoid =
  Presentation
    { presName = "Monoid"
    , presSig = sigMonoid
    , presEqs = [eqUnitL, eqAssoc]
    }
