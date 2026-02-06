{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Surface.Spec
  ( PolySurfaceDef(..)
  , SurfaceSpec(..)
  , VarDiscipline(..)
  , StructuralSpec(..)
  , LexerSpec(..)
  , ExprSpec(..)
  , ExprRule(..)
  , InfixAssoc(..)
  , InfixRule(..)
  , AppRule(..)
  , PatItem(..)
  , Action(..)
  , ElabRule(..)
  , TemplateExpr(..)
  , TemplateAttrArg(..)
  , AttrTemplate(..)
  , SurfaceAST(..)
  ) where

import Data.Text (Text)
import qualified Data.Map.Strict as M
import Strat.Poly.ModeTheory (ModeName)
import Strat.Poly.Names (GenName)
import Strat.Poly.DSL.AST (RawPolyTypeExpr)
import Strat.Poly.Attr (AttrLit)

data PolySurfaceDef = PolySurfaceDef
  { psName :: Text
  , psDoctrine :: Text
  , psMode :: ModeName
  , psSpec :: SurfaceSpec
  } deriving (Eq, Show)

data SurfaceSpec = SurfaceSpec
  { ssName :: Text
  , ssDoctrine :: Text
  , ssMode :: Text
  , ssContext :: Maybe (Text, RawPolyTypeExpr)
  , ssStructural :: StructuralSpec
  , ssLexer :: Maybe LexerSpec
  , ssExprSpec :: Maybe ExprSpec
  , ssElabRules :: M.Map Text ElabRule
  } deriving (Eq, Show)

data VarDiscipline
  = Linear
  | Affine
  | Relevant
  | Cartesian
  deriving (Eq, Show)

data StructuralSpec = StructuralSpec
  { ssDiscipline :: VarDiscipline
  , ssDupGen :: Maybe GenName
  , ssDropGen :: Maybe GenName
  } deriving (Eq, Show)

data LexerSpec = LexerSpec
  { lsKeywords :: [Text]
  , lsSymbols :: [Text]
  } deriving (Eq, Show)

data ExprSpec = ExprSpec
  { esAtoms :: [ExprRule]
  , esPrefixes :: [ExprRule]
  , esInfixes :: [InfixRule]
  , esApp :: Maybe AppRule
  } deriving (Eq, Show)

data ExprRule = ExprRule
  { erPattern :: [PatItem]
  , erAction :: Action
  } deriving (Eq, Show)

data InfixAssoc = AssocL | AssocR
  deriving (Eq, Show)

data InfixRule = InfixRule
  { irAssoc :: InfixAssoc
  , irPrec :: Int
  , irToken :: Text
  , irAction :: Action
  } deriving (Eq, Show)

newtype AppRule = AppRule
  { arAction :: Action
  } deriving (Eq, Show)

data PatItem
  = PatLit Text
  | PatIdent
  | PatInt
  | PatString
  | PatBool
  | PatExpr
  | PatType
  deriving (Eq, Show)

data Action
  = ActionCtor Text [Text]
  | ActionExpr
  deriving (Eq, Show)

data ElabRule = ElabRule
  { erCtor :: Text
  , erArgs :: [Text]
  , erTemplate :: TemplateExpr
  } deriving (Eq, Show)

data TemplateExpr
  = TId [RawPolyTypeExpr]
  | TGen Text (Maybe [RawPolyTypeExpr]) (Maybe [TemplateAttrArg])
  | TBox Text TemplateExpr
  | TLoop TemplateExpr
  | TComp TemplateExpr TemplateExpr
  | TTensor TemplateExpr TemplateExpr
  | THole Int
  | TVar Text
  deriving (Eq, Show)

data TemplateAttrArg
  = TAName Text AttrTemplate
  | TAPos AttrTemplate
  deriving (Eq, Show)

data AttrTemplate
  = ATLIT AttrLit
  | ATHole Text
  | ATVar Text
  deriving (Eq, Show)

data SurfaceAST
  = SAIdent Text
  | SALit AttrLit
  | SAType RawPolyTypeExpr
  | SANode Text [SurfaceAST]
  deriving (Eq, Show)
