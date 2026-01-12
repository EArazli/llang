module Strat.Meta.DSL.AST where

import Strat.Meta.Types
import Data.Text (Text)
import qualified Data.Map.Strict as M

data RawTerm
  = RVar Text
  | RApp Text [RawTerm]
  deriving (Eq, Show)

data RawRule = RawRule
  { rrClass  :: RuleClass
  , rrName   :: Text
  , rrOrient :: Orientation
  , rrLHS    :: RawTerm
  , rrRHS    :: RawTerm
  }
  deriving (Eq, Show)

data RawDecl
  = DeclWhere Text [RawRule]
  | DeclExpr  Text RawExpr
  deriving (Eq, Show)

data RawExpr
  = ERef Text
  | EInst Text Text
  | EAnd RawExpr RawExpr
  | ERenameSyms (M.Map Text Text) RawExpr
  | ERenameEqs  (M.Map Text Text) RawExpr
  | EShareSyms  [(Text, Text)] RawExpr
  deriving (Eq, Show)

newtype RawFile = RawFile [RawDecl]
  deriving (Eq, Show)
