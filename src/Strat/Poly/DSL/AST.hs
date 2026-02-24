module Strat.Poly.DSL.AST
  ( RawPolyDoctrine(..)
  , RawPolyItem(..)
  , RawClassifiedByDecl(..)
  , RawModeDecl(..)
  , RawModExpr(..)
  , RawModalityDecl(..)
  , RawModEqDecl(..)
  , RawModTransformDecl(..)
  , RawActionDecl(..)
  , RawObligationDecl(..)
  , RawOblExpr(..)
  , RawAttrSortDecl(..)
  , RawParamDecl(..)
  , RawTmVarDecl(..)
  , RawPolyCtorDecl(..)
  , RawPolyDataDecl(..)
  , RawPolyGenDecl(..)
  , RawPolyRuleDecl(..)
  , RawInputShape(..)
  , RawBinderVarDecl(..)
  , RawTypeRef(..)
  , RawTyVarDecl(..)
  , RawPolyObjExpr(..)
  , RawPolyContext
  , RawDiagExpr(..)
  , RawBinderArg(..)
  , RawAttrArg(..)
  , RawAttrTerm(..)
  ) where

import Data.Text (Text)
import Strat.Common.Rules (RuleClass, Orientation)


data RawPolyDoctrine = RawPolyDoctrine
  { rpdName :: Text
  , rpdExtends :: Maybe Text
  , rpdItems :: [RawPolyItem]
  } deriving (Eq, Show)

data RawPolyItem
  = RPMode RawModeDecl
  | RPModality RawModalityDecl
  | RPModEq RawModEqDecl
  | RPModTransform RawModTransformDecl
  | RPAction RawActionDecl
  | RPObligation RawObligationDecl
  | RPAttrSort RawAttrSortDecl
  | RPData RawPolyDataDecl
  | RPGen RawPolyGenDecl
  | RPRule RawPolyRuleDecl
  deriving (Eq, Show)

data RawModeDecl = RawModeDecl
  { rmdName :: Text
  , rmdAcyclic :: Bool
  , rmdClassifiedBy :: Maybe RawClassifiedByDecl
  } deriving (Eq, Show)

data RawClassifiedByDecl = RawClassifiedByDecl
  { rcdClassifier :: Text
  , rcdUniverse :: RawPolyObjExpr
  , rcdTag :: Maybe Text
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

data RawModEqDecl = RawModEqDecl
  { rmeLHS :: RawModExpr
  , rmeRHS :: RawModExpr
  } deriving (Eq, Show)

data RawModTransformDecl = RawModTransformDecl
  { rmtName :: Text
  , rmtFrom :: RawModExpr
  , rmtTo :: RawModExpr
  , rmtWitness :: Maybe Text
  } deriving (Eq, Show)

data RawActionDecl = RawActionDecl
  { radModName :: Text
  , radGenMap :: [(Text, RawDiagExpr)]
  } deriving (Eq, Show)

data RawObligationDecl = RawObligationDecl
  { rodName :: Text
  , rodForGen :: Bool
  , rodVars :: [RawParamDecl]
  , rodDom :: RawPolyContext
  , rodCod :: RawPolyContext
  , rodMode :: Text
  , rodLHS :: RawOblExpr
  , rodRHS :: RawOblExpr
  } deriving (Eq, Show)

data RawOblExpr
  = ROEDiag RawDiagExpr
  | ROEMap RawModExpr RawOblExpr
  | ROEGen
  | ROELiftDom RawDiagExpr
  | ROELiftCod RawDiagExpr
  | ROEComp RawOblExpr RawOblExpr
  | ROETensor RawOblExpr RawOblExpr
  deriving (Eq, Show)

data RawAttrSortDecl = RawAttrSortDecl
  { rasName :: Text
  , rasKind :: Maybe Text
  } deriving (Eq, Show)

data RawParamDecl
  = RPDType RawTyVarDecl
  | RPDTerm RawTmVarDecl
  deriving (Eq, Show)

data RawTmVarDecl = RawTmVarDecl
  { rtvdName :: Text
  , rtvdSort :: RawPolyObjExpr
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
  = RIPort RawPolyObjExpr
  | RIBinder [RawBinderVarDecl] RawPolyContext
  deriving (Eq, Show)

data RawBinderVarDecl = RawBinderVarDecl
  { rbvName :: Text
  , rbvType :: RawPolyObjExpr
  } deriving (Eq, Show)

data RawTypeRef = RawTypeRef
  { rtrMode :: Maybe Text
  , rtrName :: Text
  } deriving (Eq, Show)

data RawTyVarDecl = RawTyVarDecl
  { rtvName :: Text
  , rtvMode :: Maybe Text
  } deriving (Eq, Show)

data RawPolyObjExpr
  = RPTVar Text
  | RPTCon RawTypeRef [RawPolyObjExpr]
  | RPTMod RawModExpr RawPolyObjExpr
  deriving (Eq, Show)

type RawPolyContext = [RawPolyObjExpr]

data RawDiagExpr
  = RDId RawPolyContext
  | RDMetaVar Text
  | RDGen Text (Maybe [RawPolyObjExpr]) (Maybe [RawAttrArg]) (Maybe [RawBinderArg])
  | RDTermRef Text
  | RDSplice Text
  | RDBox Text RawDiagExpr
  | RDLoop RawDiagExpr
  | RDMap RawModExpr RawDiagExpr
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
