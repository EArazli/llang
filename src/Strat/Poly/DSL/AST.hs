module Strat.Poly.DSL.AST
  ( RawPolyDoctrine(..)
  , RawPolyItem(..)
  , RawModeDecl(..)
  , RawIndexFunDecl(..)
  , RawIndexRuleDecl(..)
  , RawModExpr(..)
  , RawModalityDecl(..)
  , RawStructureDecl(..)
  , RawModEqDecl(..)
  , RawAdjDecl(..)
  , RawAttrSortDecl(..)
  , RawParamDecl(..)
  , RawIxVarDecl(..)
  , RawPolyTypeDecl(..)
  , RawPolyCtorDecl(..)
  , RawPolyDataDecl(..)
  , RawPolyGenDecl(..)
  , RawPolyRuleDecl(..)
  , RawInputShape(..)
  , RawBinderVarDecl(..)
  , RawTypeRef(..)
  , RawTyVarDecl(..)
  , RawPolyTypeExpr(..)
  , RawPolyContext
  , RawDiagExpr(..)
  , RawBinderArg(..)
  , RawAttrArg(..)
  , RawAttrTerm(..)
  ) where

import Data.Text (Text)
import Strat.Common.Rules (RuleClass, Orientation)
import Strat.Poly.ModeTheory (VarDiscipline)


data RawPolyDoctrine = RawPolyDoctrine
  { rpdName :: Text
  , rpdExtends :: Maybe Text
  , rpdItems :: [RawPolyItem]
  } deriving (Eq, Show)

data RawPolyItem
  = RPMode RawModeDecl
  | RPIndexMode Text
  | RPIndexFun RawIndexFunDecl
  | RPIndexRule RawIndexRuleDecl
  | RPStructure RawStructureDecl
  | RPModality RawModalityDecl
  | RPModEq RawModEqDecl
  | RPAdjunction RawAdjDecl
  | RPAttrSort RawAttrSortDecl
  | RPType RawPolyTypeDecl
  | RPData RawPolyDataDecl
  | RPGen RawPolyGenDecl
  | RPRule RawPolyRuleDecl
  deriving (Eq, Show)

data RawModeDecl = RawModeDecl
  { rmdName :: Text
  , rmdAcyclic :: Bool
  } deriving (Eq, Show)

data RawModExpr
  = RMId Text
  | RMComp [Text]
  deriving (Eq, Show)

data RawModalityDecl = RawModalityDecl
  { rmodName :: Text
  , rmodSrc :: Text
  , rmodTgt :: Text
  } deriving (Eq, Show)

data RawStructureDecl = RawStructureDecl
  { rsMode :: Text
  , rsDisc :: VarDiscipline
  } deriving (Eq, Show)

data RawModEqDecl = RawModEqDecl
  { rmeLHS :: RawModExpr
  , rmeRHS :: RawModExpr
  } deriving (Eq, Show)

data RawAdjDecl = RawAdjDecl
  { raLeft :: Text
  , raRight :: Text
  } deriving (Eq, Show)

data RawAttrSortDecl = RawAttrSortDecl
  { rasName :: Text
  , rasKind :: Maybe Text
  } deriving (Eq, Show)

data RawParamDecl
  = RPDType RawTyVarDecl
  | RPDIndex RawIxVarDecl
  deriving (Eq, Show)

data RawIxVarDecl = RawIxVarDecl
  { rivName :: Text
  , rivSort :: RawPolyTypeExpr
  } deriving (Eq, Show)

data RawIndexFunDecl = RawIndexFunDecl
  { rifName :: Text
  , rifArgs :: [RawIxVarDecl]
  , rifRes :: RawPolyTypeExpr
  , rifMode :: Text
  } deriving (Eq, Show)

data RawIndexRuleDecl = RawIndexRuleDecl
  { rirName :: Text
  , rirVars :: [RawIxVarDecl]
  , rirLHS :: RawPolyTypeExpr
  , rirRHS :: RawPolyTypeExpr
  , rirMode :: Text
  } deriving (Eq, Show)

data RawPolyTypeDecl = RawPolyTypeDecl
  { rptName :: Text
  , rptVars :: [RawParamDecl]
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
  , rpgVars :: [RawParamDecl]
  , rpgAttrs :: [(Text, Text)]
  , rpgDom :: [RawInputShape]
  , rpgCod :: RawPolyContext
  , rpgMode :: Text
  } deriving (Eq, Show)

data RawPolyRuleDecl = RawPolyRuleDecl
  { rprClass :: RuleClass
  , rprName :: Text
  , rprOrient :: Orientation
  , rprVars :: [RawParamDecl]
  , rprDom :: RawPolyContext
  , rprCod :: RawPolyContext
  , rprMode :: Text
  , rprLHS :: RawDiagExpr
  , rprRHS :: RawDiagExpr
  } deriving (Eq, Show)

data RawInputShape
  = RIPort RawPolyTypeExpr
  | RIBinder [RawBinderVarDecl] RawPolyContext
  deriving (Eq, Show)

data RawBinderVarDecl = RawBinderVarDecl
  { rbvName :: Text
  , rbvType :: RawPolyTypeExpr
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
  | RPTBound Int
  | RPTCon RawTypeRef [RawPolyTypeExpr]
  | RPTMod RawModExpr RawPolyTypeExpr
  deriving (Eq, Show)

type RawPolyContext = [RawPolyTypeExpr]

data RawDiagExpr
  = RDId RawPolyContext
  | RDMetaVar Text
  | RDGen Text (Maybe [RawPolyTypeExpr]) (Maybe [RawAttrArg]) (Maybe [RawBinderArg])
  | RDTermRef Text
  | RDSplice Text
  | RDBox Text RawDiagExpr
  | RDLoop RawDiagExpr
  | RDComp RawDiagExpr RawDiagExpr
  | RDTensor RawDiagExpr RawDiagExpr
  deriving (Eq, Show)

data RawBinderArg
  = RBAExpr RawDiagExpr
  | RBAMeta Text
  deriving (Eq, Show)

data RawAttrArg
  = RAName Text RawAttrTerm
  | RAPos RawAttrTerm
  deriving (Eq, Show)

data RawAttrTerm
  = RATVar Text
  | RATInt Int
  | RATString Text
  | RATBool Bool
  deriving (Eq, Show)
