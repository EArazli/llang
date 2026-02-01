module Strat.Poly.DSL.AST
  ( RawPolyDoctrine(..)
  , RawPolyItem(..)
  , RawPolyTypeDecl(..)
  , RawPolyCtorDecl(..)
  , RawPolyDataDecl(..)
  , RawPolyGenDecl(..)
  , RawPolyRuleDecl(..)
  , RawTypeRef(..)
  , RawTyVarDecl(..)
  , RawPolyTypeExpr(..)
  , RawPolyContext
  , RawDiagExpr(..)
  ) where

import Data.Text (Text)
import Strat.Common.Rules (RuleClass, Orientation)


data RawPolyDoctrine = RawPolyDoctrine
  { rpdName :: Text
  , rpdExtends :: Maybe Text
  , rpdItems :: [RawPolyItem]
  } deriving (Eq, Show)

data RawPolyItem
  = RPMode Text
  | RPType RawPolyTypeDecl
  | RPData RawPolyDataDecl
  | RPGen RawPolyGenDecl
  | RPRule RawPolyRuleDecl
  deriving (Eq, Show)

data RawPolyTypeDecl = RawPolyTypeDecl
  { rptName :: Text
  , rptVars :: [RawTyVarDecl]
  , rptMode :: Text
  } deriving (Eq, Show)

data RawPolyCtorDecl = RawPolyCtorDecl
  { rpcName :: Text
  , rpcArgs :: RawPolyContext
  } deriving (Eq, Show)

data RawPolyDataDecl = RawPolyDataDecl
  { rpdTyName :: Text
  , rpdTyVars :: [RawTyVarDecl]
  , rpdTyMode :: Text
  , rpdCtors :: [RawPolyCtorDecl]
  } deriving (Eq, Show)

data RawPolyGenDecl = RawPolyGenDecl
  { rpgName :: Text
  , rpgVars :: [RawTyVarDecl]
  , rpgDom :: RawPolyContext
  , rpgCod :: RawPolyContext
  , rpgMode :: Text
  } deriving (Eq, Show)

data RawPolyRuleDecl = RawPolyRuleDecl
  { rprClass :: RuleClass
  , rprName :: Text
  , rprOrient :: Orientation
  , rprVars :: [RawTyVarDecl]
  , rprDom :: RawPolyContext
  , rprCod :: RawPolyContext
  , rprMode :: Text
  , rprLHS :: RawDiagExpr
  , rprRHS :: RawDiagExpr
  } deriving (Eq, Show)

data RawTypeRef = RawTypeRef
  { rtrMode :: Maybe Text
  , rtrName :: Text
  } deriving (Eq, Show)

data RawTyVarDecl = RawTyVarDecl
  { rtvName :: Text
  , rtvMode :: Maybe Text
  } deriving (Eq, Show)

data RawPolyTypeExpr
  = RPTVar Text
  | RPTCon RawTypeRef [RawPolyTypeExpr]
  deriving (Eq, Show)

type RawPolyContext = [RawPolyTypeExpr]

data RawDiagExpr
  = RDId RawPolyContext
  | RDGen Text (Maybe [RawPolyTypeExpr])
  | RDTermRef Text
  | RDBox Text RawDiagExpr
  | RDLoop RawDiagExpr
  | RDComp RawDiagExpr RawDiagExpr
  | RDTensor RawDiagExpr RawDiagExpr
  deriving (Eq, Show)
