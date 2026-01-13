module Strat.Kernel.DSL.AST
  ( RawTerm(..)
  , RawSort(..)
  , RawBinder(..)
  , RawSortDecl(..)
  , RawOpDecl(..)
  , RawRule(..)
  , RawItem(..)
  , RawDecl(..)
  , RawExpr(..)
  , RawFile(..)
  ) where

import Strat.Kernel.Types
import Data.Text (Text)
import qualified Data.Map.Strict as M

data RawTerm
  = RVar Text
  | RApp Text [RawTerm]
  deriving (Eq, Show)

data RawSort = RawSort Text [RawTerm]
  deriving (Eq, Show)

data RawBinder = RawBinder
  { rbName :: Text
  , rbSort :: RawSort
  }
  deriving (Eq, Show)

data RawSortDecl = RawSortDecl
  { rsName   :: Text
  , rsParams :: [RawSort]
  }
  deriving (Eq, Show)

data RawOpDecl = RawOpDecl
  { roName   :: Text
  , roTele   :: [RawBinder]
  , roResult :: RawSort
  }
  deriving (Eq, Show)

data RawRule = RawRule
  { rrClass  :: RuleClass
  , rrName   :: Text
  , rrOrient :: Orientation
  , rrTele   :: [RawBinder]
  , rrLHS    :: RawTerm
  , rrRHS    :: RawTerm
  }
  deriving (Eq, Show)

data RawItem
  = ItemSort RawSortDecl
  | ItemOp   RawOpDecl
  | ItemRule RawRule
  deriving (Eq, Show)

data RawDecl
  = DeclWhere Text [RawItem]
  | DeclExpr  Text RawExpr
  deriving (Eq, Show)

data RawExpr
  = ERef Text
  | EInst Text Text
  | EAnd RawExpr RawExpr
  | ERenameOps   (M.Map Text Text) RawExpr
  | ERenameSorts (M.Map Text Text) RawExpr
  | ERenameEqs   (M.Map Text Text) RawExpr
  | EShareOps    [(Text, Text)] RawExpr
  | EShareSorts  [(Text, Text)] RawExpr
  deriving (Eq, Show)

newtype RawFile = RawFile [RawDecl]
  deriving (Eq, Show)
