module Strat.Kernel.Signature where

import Strat.Kernel.Syntax
import qualified Data.Map.Strict as M

data SortCtor = SortCtor
  { scName      :: SortName
  , scParamSort :: [Sort]
  }
  deriving (Eq, Show)

data OpDecl = OpDecl
  { opName   :: OpName
  , opTele   :: [Binder]
  , opResult :: Sort
  }
  deriving (Eq, Show)

data Signature = Signature
  { sigSortCtors :: M.Map SortName SortCtor
  , sigOps       :: M.Map OpName OpDecl
  }
  deriving (Eq, Show)
