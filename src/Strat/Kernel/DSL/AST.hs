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
  , RawSyntaxItem(..)
  , RawNotation(..)
  , RawAssoc(..)
  , RawModelItem(..)
  , RawDefault(..)
  , RawModelClause(..)
  , RawRun(..)
  , RawRunShow(..)
  , RawFile(..)
  ) where

import Strat.Kernel.Types
import Strat.Model.Spec (MExpr)
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
  = DeclImport FilePath
  | DeclWhere Text [RawItem]
  | DeclExpr  Text RawExpr
  | DeclSyntaxWhere Text [RawSyntaxItem]
  | DeclModelWhere Text [RawModelItem]
  | DeclRun RawRun
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


data RawSyntaxItem
  = RSPrint RawNotation
  | RSParse RawNotation
  | RSAllowCall
  | RSVarPrefix Text
  deriving (Eq, Show)


data RawNotation
  = RNAtom Text Text
  | RNPrefix Int Text Text
  | RNPostfix Int Text Text
  | RNInfix RawAssoc Int Text Text
  deriving (Eq, Show)


data RawAssoc = AssocL | AssocR | AssocN
  deriving (Eq, Show)


data RawModelItem
  = RMDefault RawDefault
  | RMOp RawModelClause
  deriving (Eq, Show)


data RawDefault
  = RawDefaultSymbolic
  | RawDefaultError Text
  deriving (Eq, Show)


data RawModelClause = RawModelClause
  { rmcOp   :: Text
  , rmcArgs :: [Text]
  , rmcExpr :: MExpr
  }
  deriving (Eq, Show)


data RawRunShow
  = RawShowNormalized
  | RawShowValue
  | RawShowCat
  deriving (Eq, Ord, Show)


data RawRun = RawRun
  { rrDoctrine  :: Maybe RawExpr
  , rrSyntax    :: Maybe Text
  , rrModel     :: Maybe Text
  , rrOpen      :: [Text]
  , rrPolicy    :: Maybe Text
  , rrFuel      :: Maybe Int
  , rrShowFlags :: [RawRunShow]
  , rrExprText  :: Text
  }
  deriving (Eq, Show)

newtype RawFile = RawFile [RawDecl]
  deriving (Eq, Show)
