module Strat.Poly.DSL.AST
  ( RawPolyDoctrine(..)
  , RawPolyItem(..)
  , RawClassifiedByDecl(..)
  , RawCompDecl(..)
  , RawDefEqEngine(..)
  , RawModeDecl(..)
  , RawClassifierLiftDecl(..)
  , RawModExpr(..)
  , RawModalityDecl(..)
  , RawModEqDecl(..)
  , RawModTransformDecl(..)
  , RawActionDecl(..)
  , RawObligationDecl(..)
  , RawOblExpr(..)
  , RawLiteralDecl(..)
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
  , RawGenArg(..)
  , RawBinderArg(..)
  ) where

import Data.Text (Text)
import Strat.Common.Rules (RuleClass, Orientation)
import Strat.Poly.Literal (Literal, LiteralKind)


data RawPolyDoctrine = RawPolyDoctrine
  { rpdName :: Text
  , rpdExtends :: Maybe Text
  , rpdItems :: [RawPolyItem]
  } deriving (Eq, Read, Show)

data RawPolyItem
  = RPMode RawModeDecl
  | RPComprehension RawCompDecl
  | RPClassifierLift RawClassifierLiftDecl
  | RPModality RawModalityDecl
  | RPModEq RawModEqDecl
  | RPModTransform RawModTransformDecl
  | RPAction RawActionDecl
  | RPObligation RawObligationDecl
  | RPLiteral RawLiteralDecl
  | RPData RawPolyDataDecl
  | RPGen RawPolyGenDecl
  | RPRule RawPolyRuleDecl
  deriving (Eq, Read, Show)

data RawCompDecl = RawCompDecl
  { rcmpMode :: Text
  , rcmpCtxExt :: Text
  , rcmpVar :: Text
  , rcmpReindex :: Text
  } deriving (Eq, Read, Show)

data RawDefEqEngine
  = RDETRS
  | RDENBE
  deriving (Eq, Read, Show)

data RawModeDecl = RawModeDecl
  { rmdName :: Text
  , rmdAcyclic :: Bool
  , rmdDefEqEngine :: Maybe RawDefEqEngine
  , rmdClassifiedBy :: Maybe RawClassifiedByDecl
  } deriving (Eq, Read, Show)

data RawClassifierLiftDecl = RawClassifierLiftDecl
  { rclModality :: Text
  , rclLift :: RawModExpr
  } deriving (Eq, Read, Show)

data RawClassifiedByDecl = RawClassifiedByDecl
  { rcdClassifier :: Text
  , rcdUniverse :: RawPolyObjExpr
  } deriving (Eq, Read, Show)

data RawModExpr
  = RMId Text
  | RMComp [Text]
  deriving (Eq, Read, Show)

data RawModalityDecl = RawModalityDecl
  { rmodName :: Text
  , rmodSrc :: Text
  , rmodTgt :: Text
  } deriving (Eq, Read, Show)

data RawModEqDecl = RawModEqDecl
  { rmeLHS :: RawModExpr
  , rmeRHS :: RawModExpr
  } deriving (Eq, Read, Show)

data RawModTransformDecl = RawModTransformDecl
  { rmtName :: Text
  , rmtFrom :: RawModExpr
  , rmtTo :: RawModExpr
  , rmtWitness :: Maybe Text
  } deriving (Eq, Read, Show)

data RawActionDecl = RawActionDecl
  { radModName :: Text
  , radGenMap :: [(Text, RawDiagExpr)]
  } deriving (Eq, Read, Show)

data RawObligationDecl = RawObligationDecl
  { rodName :: Text
  , rodForGen :: Bool
  , rodVars :: [RawParamDecl]
  , rodDom :: RawPolyContext
  , rodCod :: RawPolyContext
  , rodMode :: Text
  , rodLHS :: RawOblExpr
  , rodRHS :: RawOblExpr
  } deriving (Eq, Read, Show)

data RawOblExpr
  = ROEDiag RawDiagExpr
  | ROEMap RawModExpr RawOblExpr
  | ROEGen
  | ROELiftDom RawDiagExpr
  | ROELiftCod RawDiagExpr
  | ROEComp RawOblExpr RawOblExpr
  | ROETensor RawOblExpr RawOblExpr
  deriving (Eq, Read, Show)

data RawLiteralDecl = RawLiteralDecl
  { rldTypeName :: Text
  , rldOwnerMode :: Text
  , rldKind :: LiteralKind
  } deriving (Eq, Read, Show)

data RawParamDecl
  = RPDType RawTyVarDecl
  | RPDTerm RawTmVarDecl
  deriving (Eq, Read, Show)

data RawTmVarDecl = RawTmVarDecl
  { rtvdName :: Text
  , rtvdSort :: RawPolyObjExpr
  } deriving (Eq, Read, Show)

data RawPolyCtorDecl = RawPolyCtorDecl
  { rpcName :: Text
  , rpcArgs :: RawPolyContext
  } deriving (Eq, Read, Show)

data RawPolyDataDecl = RawPolyDataDecl
  { rpdTyName :: Text
  , rpdTyVars :: [RawTyVarDecl]
  , rpdTyMode :: Text
  , rpdCtors :: [RawPolyCtorDecl]
  } deriving (Eq, Read, Show)

data RawPolyGenDecl = RawPolyGenDecl
  { rpgName :: Text
  , rpgVars :: [RawParamDecl]
  , rpgDom :: [RawInputShape]
  , rpgCod :: RawPolyContext
  , rpgMode :: Text
  } deriving (Eq, Read, Show)

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
  } deriving (Eq, Read, Show)

data RawInputShape
  = RIPort RawPolyObjExpr
  | RIBinder [RawBinderVarDecl] RawPolyContext
  deriving (Eq, Read, Show)

data RawBinderVarDecl = RawBinderVarDecl
  { rbvName :: Text
  , rbvType :: RawPolyObjExpr
  } deriving (Eq, Read, Show)

data RawTypeRef = RawTypeRef
  { rtrMode :: Maybe Text
  , rtrName :: Text
  } deriving (Eq, Read, Show)

data RawTyVarDecl = RawTyVarDecl
  { rtvName :: Text
  , rtvMode :: Maybe Text
  } deriving (Eq, Read, Show)

data RawPolyObjExpr
  = RPTVar Text
  | RPTCon RawTypeRef [RawPolyObjExpr]
  | RPTMod RawModExpr RawPolyObjExpr
  | RPLit Literal
  deriving (Eq, Read, Show)

type RawPolyContext = [RawPolyObjExpr]

data RawDiagExpr
  = RDId RawPolyContext
  | RDMetaVar Text
  | RDGen Text (Maybe [RawGenArg]) (Maybe [RawBinderArg])
  | RDSplice Text
  | RDBox Text RawDiagExpr
  | RDTrace Int RawDiagExpr
  | RDLoop RawDiagExpr
  | RDMap RawModExpr RawDiagExpr
  | RDComp RawDiagExpr RawDiagExpr
  | RDTensor RawDiagExpr RawDiagExpr
  deriving (Eq, Read, Show)

data RawBinderArg
  = RBAExpr RawDiagExpr
  | RBAMeta Text
  deriving (Eq, Read, Show)

data RawGenArg
  = RGPos RawPolyObjExpr
  | RGNamed Text RawPolyObjExpr
  deriving (Eq, Read, Show)
