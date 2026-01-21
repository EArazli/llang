module Strat.Surface2.Def
  ( SurfaceDef(..)
  , SurfaceRequire(..)
  , ParamSort(..)
  , ConDecl(..)
  , ConArg(..)
  , JudgDecl(..)
  , JudgParam(..)
  , RuleDef(..)
  , RulePremise(..)
  , RuleConclusion(..)
  , UnderCtx(..)
  , ArgPat(..)
  , Define(..)
  , DefineClause(..)
  , DefinePat(..)
  , WhereClause(..)
  , CtxPat(..)
  , NatPat(..)
  , CoreExpr(..)
  ) where

import Strat.Surface2.Term
import Strat.Surface2.Pattern
import Strat.Kernel.Presentation (Presentation)
import Data.Text (Text)
import qualified Data.Map.Strict as M

data SurfaceDef = SurfaceDef
  { sdName :: Text
  , sdSorts :: M.Map Sort2Name ()
  , sdContextSort :: Sort2Name
  , sdCons :: M.Map Con2Name ConDecl
  , sdJudgments :: M.Map JudgName JudgDecl
  , sdRules :: [RuleDef]
  , sdDefines :: M.Map Text Define
  , sdRequires :: [SurfaceRequire]
  } deriving (Eq, Show)

data SurfaceRequire = SurfaceRequire
  { srAlias :: Text
  , srPres  :: Presentation
  } deriving (Eq, Show)

data ParamSort
  = PSurf Sort2Name
  | PCtx
  | PCore
  | PNat
  deriving (Eq, Ord, Show)

data ConDecl = ConDecl
  { conName :: Con2Name
  , conArgs :: [ConArg]
  , conResult :: Sort2Name
  } deriving (Eq, Show)

data ConArg = ConArg
  { caName :: Text
  , caBinders :: [STerm]
  , caSort :: Sort2Name
  } deriving (Eq, Show)

data JudgDecl = JudgDecl
  { jdName :: JudgName
  , jdParams :: [JudgParam]
  , jdOutputs :: [JudgParam]
  } deriving (Eq, Show)

data JudgParam = JudgParam
  { jpName :: Text
  , jpSort :: ParamSort
  } deriving (Eq, Show)

data RuleDef = RuleDef
  { rdName :: Text
  , rdPremises :: [RulePremise]
  , rdConclusion :: RuleConclusion
  } deriving (Eq, Show)

data RulePremise
  = PremiseJudg
      { pjJudg :: JudgName
      , pjArgs :: [ArgPat]
      , pjOutputs :: [Text]
      , pjUnder :: Maybe UnderCtx
      }
  | PremiseLookup
      { plCtxVar :: Text
      , plIndex :: NatPat
      , plOut :: Text
      }
  deriving (Eq, Show)

data RuleConclusion = RuleConclusion
  { rcJudg :: JudgName
  , rcArgs :: [ArgPat]
  , rcOutputs :: [CoreExpr]
  } deriving (Eq, Show)

data UnderCtx = UnderCtx
  { ucCtx :: Text
  , ucName :: Text
  , ucType :: PTerm
  } deriving (Eq, Show)

data ArgPat
  = ArgSurf PTerm
  | ArgCtx Text
  | ArgNat NatPat
  deriving (Eq, Show)

data Define = Define
  { defName :: Text
  , defClauses :: [DefineClause]
  } deriving (Eq, Show)

data DefineClause = DefineClause
  { dcArgs :: [DefinePat]
  , dcBody :: CoreExpr
  , dcWhere :: [WhereClause]
  } deriving (Eq, Show)

data DefinePat
  = DPVar Text
  | DPSurf PTerm
  | DPCtx CtxPat
  | DPNat NatPat
  deriving (Eq, Show)

data WhereClause = WhereClause
  { wcName :: Text
  , wcPat :: CtxPat
  } deriving (Eq, Show)

data CtxPat
  = CtxEmpty
  | CtxVar Text
  | CtxExtend Text Text PTerm
  deriving (Eq, Show)

data NatPat
  = NatZero
  | NatSucc Text
  | NatVar Text
  deriving (Eq, Show)

data CoreExpr
  = CoreVar Text
  | CoreApp Text [CoreExpr]
  deriving (Eq, Show)
