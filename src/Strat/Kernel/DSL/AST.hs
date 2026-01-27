module Strat.Kernel.DSL.AST
  ( RawTerm(..)
  , RawSort(..)
  , RawBinder(..)
  , RawSortDecl(..)
  , RawOpDecl(..)
  , RawRule(..)
  , RawItem(..)
  , RawDecl(..)
  , RawSyntaxDecl(..)
  , RawSyntaxTarget(..)
  , RawSyntaxItem(..)
  , RawNotation(..)
  , RawAssoc(..)
  , RawModelItem(..)
  , RawDefault(..)
  , RawModelClause(..)
  , RawSurfaceDecl(..)
  , RawSurfaceItem(..)
  , RawSurfaceCon(..)
  , RawSurfaceArg(..)
  , RawSurfaceJudg(..)
  , RawSurfaceJudgParam(..)
  , RawSurfaceRule(..)
  , RawSurfacePremise(..)
  , RawSurfaceConclusion(..)
  , RawSurfaceTerm(..)
  , RawSurfacePat(..)
  , RawCtxPat(..)
  , RawNatPat(..)
  , RawDefine(..)
  , RawDefineClause(..)
  , RawDefinePat(..)
  , RawWhereClause(..)
  , RawCoreExpr(..)
  , RawSurfaceNotation(..)
  , RawSurfaceAssoc(..)
  , RawMorphismDecl(..)
  , RawMorphismItem(..)
  , RawMorphismCheck(..)
  , RawPolyMorphism(..)
  , RawPolyMorphismItem(..)
  , RawPolyTypeMap(..)
  , RawPolyGenMap(..)
  , RawPolySurfaceDecl(..)
  , RawImplementsDecl(..)
  , RawRun(..)
  , RawRunSpec(..)
  , RawNamedRun(..)
  , RawRunShow(..)
  , RawPolyRun(..)
  , RawFile(..)
  ) where

import Strat.Kernel.Types
import Strat.Model.Spec (MExpr)
import Data.Text (Text)
import qualified Strat.Poly.DSL.AST as PolyAST


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
  , rsTele   :: [RawBinder]
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
  | DeclDoctrineWhere Text (Maybe Text) [RawItem]
  | DeclDoctrinePushout Text Text Text
  | DeclPolyDoctrine PolyAST.RawPolyDoctrine
  | DeclPolyDoctrinePushout Text Text Text
  | DeclPolyDoctrineCoproduct Text Text Text
  | DeclPolySurface RawPolySurfaceDecl
  | DeclSyntaxWhere RawSyntaxDecl
  | DeclModelWhere Text Text [RawModelItem]
  | DeclPolyModelWhere Text Text [RawModelItem]
  | DeclSurfaceWhere RawSurfaceDecl
  | DeclMorphismWhere RawMorphismDecl
  | DeclPolyMorphism RawPolyMorphism
  | DeclImplements RawImplementsDecl
  | DeclRunSpec Text RawRunSpec
  | DeclRun RawNamedRun
  | DeclPolyRun RawPolyRun
  deriving (Eq, Show)


data RawSyntaxDecl = RawSyntaxDecl
  { rsnName :: Text
  , rsnTarget :: RawSyntaxTarget
  , rsnItems :: [RawSyntaxItem]
  } deriving (Eq, Show)

data RawSyntaxTarget
  = SyntaxDoctrine
  | SyntaxSurface Text
  deriving (Eq, Show)

data RawSyntaxItem
  = RSPrint RawNotation
  | RSParse RawNotation
  | RSTy RawSurfaceNotation
  | RSTm RawSurfaceNotation
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
  | RawShowInput
  deriving (Eq, Ord, Show)


data RawRun = RawRun
  { rrDoctrine  :: Maybe Text
  , rrSyntax    :: Maybe Text
  , rrSurface   :: Maybe Text
  , rrSurfaceSyntax :: Maybe Text
  , rrModel     :: Maybe Text
  , rrUses      :: [(Text, Text)]
  , rrOpen      :: [Text]
  , rrPolicy    :: Maybe Text
  , rrFuel      :: Maybe Int
  , rrShowFlags :: [RawRunShow]
  , rrExprText  :: Text
  }
  deriving (Eq, Show)

data RawPolyRun = RawPolyRun
  { rprName :: Text
  , rprDoctrine :: Text
  , rprMode :: Maybe Text
  , rprSurface :: Maybe Text
  , rprModel :: Maybe Text
  , rprPolicy :: Maybe Text
  , rprFuel :: Maybe Int
  , rprShowFlags :: [RawRunShow]
  , rprExprText :: Text
  }
  deriving (Eq, Show)

data RawRunSpec = RawRunSpec
  { rrsRun :: RawRun
  }
  deriving (Eq, Show)

data RawNamedRun = RawNamedRun
  { rnrName  :: Text
  , rnrUsing :: Maybe Text
  , rnrRun   :: RawRun
  }
  deriving (Eq, Show)

data RawSurfaceDecl = RawSurfaceDecl
  { rsdName :: Text
  , rsdItems :: [RawSurfaceItem]
  } deriving (Eq, Show)

data RawSurfaceItem
  = RSRequires Text Text
  | RSDeriveContexts Text
  | RSContextSort Text
  | RSSort Text
  | RSCon RawSurfaceCon
  | RSJudg RawSurfaceJudg
  | RSRule RawSurfaceRule
  | RSDefine RawDefine
  deriving (Eq, Show)

data RawSurfaceCon = RawSurfaceCon
  { rscName :: Text
  , rscArgs :: [RawSurfaceArg]
  , rscResult :: Text
  } deriving (Eq, Show)

data RawSurfaceArg = RawSurfaceArg
  { rsaName :: Text
  , rsaBinders :: [(Text, RawSurfaceTerm)]
  , rsaSort :: Text
  } deriving (Eq, Show)

data RawSurfaceJudg = RawSurfaceJudg
  { rsjName :: Text
  , rsjParams :: [RawSurfaceJudgParam]
  , rsjOutputs :: [RawSurfaceJudgParam]
  } deriving (Eq, Show)

data RawSurfaceJudgParam = RawSurfaceJudgParam
  { rsjpName :: Text
  , rsjpSort :: Text
  } deriving (Eq, Show)

data RawSurfaceRule = RawSurfaceRule
  { rsrName :: Text
  , rsrPremises :: [RawSurfacePremise]
  , rsrConclusion :: RawSurfaceConclusion
  } deriving (Eq, Show)

data RawSurfacePremise
  = RPremiseJudg
      { rpjName :: Text
      , rpjArgs :: [RawSurfacePat]
      , rpjOutputs :: [Text]
      , rpjUnder :: Maybe (Text, Text, RawSurfaceTerm)
      }
  | RPremiseLookup
      { rplCtx :: Text
      , rplIndex :: RawNatPat
      , rplOut :: Text
      }
  deriving (Eq, Show)

data RawSurfaceConclusion = RawSurfaceConclusion
  { rcoName :: Text
  , rcoArgs :: [RawSurfacePat]
  , rcoOutputs :: [RawCoreExpr]
  } deriving (Eq, Show)

data RawSurfaceTerm
  = RSTVar Text
  | RSTBound Int
  | RSTCon Text [RawSurfaceTerm]
  deriving (Eq, Show)

data RawSurfacePat
  = RSPVar Text
  | RSPBound Int
  | RSPBoundVar Text
  | RSPCon Text [RawSurfacePat]
  deriving (Eq, Show)

data RawCtxPat
  = RCPEmpty
  | RCPVar Text
  | RCPExt Text Text RawSurfaceTerm
  deriving (Eq, Show)

data RawNatPat
  = RNPZero
  | RNPSucc Text
  | RNPVar Text
  deriving (Eq, Show)

data RawDefine = RawDefine
  { rdName :: Text
  , rdClauses :: [RawDefineClause]
  } deriving (Eq, Show)

data RawDefineClause = RawDefineClause
  { rdcArgs :: [RawDefinePat]
  , rdcBody :: RawCoreExpr
  , rdcWhere :: [RawWhereClause]
  } deriving (Eq, Show)

data RawDefinePat
  = RDPVar Text
  | RDPSurf RawSurfacePat
  | RDPCtx RawCtxPat
  | RDPNat RawNatPat
  deriving (Eq, Show)

data RawWhereClause = RawWhereClause
  { rwcName :: Text
  , rwcPat :: RawCtxPat
  } deriving (Eq, Show)

data RawCoreExpr
  = RCEVar Text
  | RCEApp Text [RawCoreExpr]
  deriving (Eq, Show)

data RawSurfaceNotation
  = RSNAtom Text Text
  | RSNPrefix Text Text
  | RSNInfix RawSurfaceAssoc Int Text Text
  | RSNBinder Text Text Text Text
  | RSNApp Text
  | RSNTuple Text Text
  deriving (Eq, Show)

data RawSurfaceAssoc = SurfAssocL | SurfAssocR | SurfAssocN
  deriving (Eq, Show)

data RawMorphismDecl = RawMorphismDecl
  { rmdName  :: Text
  , rmdSrc   :: Text
  , rmdTgt   :: Text
  , rmdItems :: [RawMorphismItem]
  , rmdCheck :: Maybe RawMorphismCheck
  } deriving (Eq, Show)

data RawMorphismItem
  = RMISort Text Text
  | RMIOp
      { rmiSrcOp  :: Text
      , rmiParams :: Maybe [Text]
      , rmiRhs    :: RawTerm
      }
  deriving (Eq, Show)

data RawMorphismCheck = RawMorphismCheck
  { rmcPolicy :: Maybe Text
  , rmcFuel   :: Maybe Int
  } deriving (Eq, Show)

data RawPolyMorphism = RawPolyMorphism
  { rpmName :: Text
  , rpmSrc :: Text
  , rpmTgt :: Text
  , rpmItems :: [RawPolyMorphismItem]
  , rpmPolicy :: Maybe Text
  , rpmFuel :: Maybe Int
  } deriving (Eq, Show)

data RawPolyMorphismItem
  = RPMType RawPolyTypeMap
  | RPMGen RawPolyGenMap
  deriving (Eq, Show)

data RawPolyTypeMap = RawPolyTypeMap
  { rpmtSrcType :: Text
  , rpmtSrcMode :: Text
  , rpmtTgtType :: PolyAST.RawPolyTypeExpr
  , rpmtTgtMode :: Text
  } deriving (Eq, Show)

data RawPolyGenMap = RawPolyGenMap
  { rpmgSrcGen :: Text
  , rpmgMode :: Text
  , rpmgRhs :: PolyAST.RawDiagExpr
  } deriving (Eq, Show)

data RawPolySurfaceDecl = RawPolySurfaceDecl
  { rpsName :: Text
  , rpsDoctrine :: Text
  , rpsMode :: Text
  } deriving (Eq, Show)

data RawImplementsDecl = RawImplementsDecl
  { ridInterface :: Text
  , ridTarget    :: Text
  , ridMorphism  :: Text
  } deriving (Eq, Show)

newtype RawFile = RawFile [RawDecl]
  deriving (Eq, Show)
