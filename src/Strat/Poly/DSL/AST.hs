module Strat.Poly.DSL.AST
  ( RawPolyDoctrine(..)
  , RawPolyItem(..)
  , RawPolyTypeDecl(..)
  , RawPolyGenDecl(..)
  , RawPolyRuleDecl(..)
  , RawPolyTypeExpr(..)
  , RawPolyContext
  , RawDiagExpr(..)
  ) where

import Data.Text (Text)
import Strat.Kernel.Types (RuleClass, Orientation)


data RawPolyDoctrine = RawPolyDoctrine
  { rpdName :: Text
  , rpdExtends :: Maybe Text
  , rpdItems :: [RawPolyItem]
  } deriving (Eq, Show)

data RawPolyItem
  = RPMode Text
  | RPType RawPolyTypeDecl
  | RPGen RawPolyGenDecl
  | RPRule RawPolyRuleDecl
  deriving (Eq, Show)

data RawPolyTypeDecl = RawPolyTypeDecl
  { rptName :: Text
  , rptVars :: [Text]
  , rptMode :: Text
  } deriving (Eq, Show)

data RawPolyGenDecl = RawPolyGenDecl
  { rpgName :: Text
  , rpgVars :: [Text]
  , rpgDom :: RawPolyContext
  , rpgCod :: RawPolyContext
  , rpgMode :: Text
  } deriving (Eq, Show)

data RawPolyRuleDecl = RawPolyRuleDecl
  { rprClass :: RuleClass
  , rprName :: Text
  , rprOrient :: Orientation
  , rprVars :: [Text]
  , rprDom :: RawPolyContext
  , rprCod :: RawPolyContext
  , rprMode :: Text
  , rprLHS :: RawDiagExpr
  , rprRHS :: RawDiagExpr
  } deriving (Eq, Show)

data RawPolyTypeExpr
  = RPTVar Text
  | RPTCon Text [RawPolyTypeExpr]
  deriving (Eq, Show)

type RawPolyContext = [RawPolyTypeExpr]

data RawDiagExpr
  = RDId RawPolyContext
  | RDGen Text (Maybe [RawPolyTypeExpr])
  | RDBox Text RawDiagExpr
  | RDComp RawDiagExpr RawDiagExpr
  | RDTensor RawDiagExpr RawDiagExpr
  deriving (Eq, Show)
