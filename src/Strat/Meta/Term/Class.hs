{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Strat.Meta.Term.Class where

import Strat.Meta.Types
import qualified Data.Map.Strict as M
import qualified Data.Set as S

-- Generic substitution mapping variables to terms
newtype Subst t = Subst { unSubst :: M.Map (Var t) t }

deriving instance (Eq t, Eq (Var t)) => Eq (Subst t)
deriving instance (Show t, Show (Var t)) => Show (Subst t)

class (Eq t, Ord (Var t)) => TermLike t where
  type Var t

  -- Observe term shape
  isVar   :: t -> Bool
  asVar   :: t -> Maybe (Var t)

  -- Enumerate positions (include [] by convention)
  positions :: t -> [Pos]

  subtermAt  :: t -> Pos -> Maybe t
  replaceAt  :: t -> Pos -> t -> Maybe t

  vars :: t -> S.Set (Var t)

  -- Apply a substitution to a term (recursive / homomorphic)
  applySubst :: Subst t -> t -> t

  -- Rename variables (used to alpha-rename rules apart if needed)
  renameVars :: (Var t -> Var t) -> t -> t

-- For rewriting: match(pattern, target) instantiates vars in pattern
class TermLike t => Matchable t where
  match :: t -> t -> Maybe (Subst t)

-- For critical pairs: unify(t1, t2) instantiates vars in both terms
-- If a term language cannot support unification, you can omit this instance
class TermLike t => Unifiable t where
  unify :: t -> t -> Maybe (Subst t)

-- For rule-scoped variables
class ScopedVar v where
  setNs :: Ns -> v -> v
