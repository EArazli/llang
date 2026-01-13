{-# LANGUAGE OverloadedStrings #-}
module Strat.Kernel.Examples.Monoid where

import Strat.Kernel.Signature
import Strat.Kernel.Syntax
import Strat.Kernel.Term
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
