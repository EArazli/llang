module Strat.Kernel.Syntax
  ( ScopeId(..)
  , Var(..)
  , SortName(..)
  , OpName(..)
  , Sort(..)
  , TermNode(..)
  , Term(..)
  , Binder(..)
  ) where

import Data.Text (Text)

newtype ScopeId = ScopeId Text
  deriving (Eq, Ord, Show)

data Var = Var
  { vScope :: ScopeId
  , vLocal :: Int
  }
  deriving (Eq, Ord, Show)

newtype SortName = SortName Text
  deriving (Eq, Ord, Show)

newtype OpName = OpName Text
  deriving (Eq, Ord, Show)

data Sort = Sort SortName [Term]
  deriving (Eq, Ord, Show)

data TermNode
  = TVar Var
  | TOp OpName [Term]
  deriving (Eq, Ord, Show)

data Term = Term
  { termSort :: Sort
  , termNode :: TermNode
  }
  deriving (Eq, Ord, Show)

data Binder = Binder
  { bVar  :: Var
  , bSort :: Sort
  }
  deriving (Eq, Ord, Show)
