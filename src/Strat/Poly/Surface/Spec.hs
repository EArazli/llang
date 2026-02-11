{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Surface.Spec
  ( PolySurfaceDef(..)
  , SurfaceSpec(..)
  , LexerSpec(..)
  , ExprSpec(..)
  , ExprRule(..)
  , BinderDecl(..)
  , InfixAssoc(..)
  , InfixRule(..)
  , AppRule(..)
  , PatItem(..)
  , Action(..)
  , GenRef(..)
  , TemplateExpr(..)
  , TemplateBinderArg(..)
  , TemplateAttrArg(..)
  , AttrTemplate(..)
  ) where

import Data.Text (Text)
import Strat.Poly.ModeTheory (ModeName)
import Strat.Poly.DSL.AST (RawPolyTypeExpr)
import Strat.Poly.Attr (AttrLit)

data PolySurfaceDef = PolySurfaceDef
  { psName :: Text
  , psDoctrine :: Text
  , psBaseDoctrine :: Maybe Text
  , psMode :: ModeName
  , psSpec :: SurfaceSpec
  } deriving (Eq, Show)

data SurfaceSpec = SurfaceSpec
  { ssName :: Text
  , ssDoctrine :: Text
  , ssBaseDoctrine :: Maybe Text
  , ssMode :: Text
  , ssLexer :: Maybe LexerSpec
  , ssExprSpec :: Maybe ExprSpec
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
  , erBinder :: Maybe BinderDecl
  } deriving (Eq, Show)

data BinderDecl
  = BindIn
      { bdVarCap :: Text
      , bdTypeCap :: Text
      , bdBodyHole :: Int
      }
  | BindLet
      { bdVarCap :: Text
      , bdValueHole :: Int
      , bdBodyHole :: Int
      }
  deriving (Eq, Show)

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
  | PatIdent (Maybe Text)
  | PatInt (Maybe Text)
  | PatString (Maybe Text)
  | PatBool (Maybe Text)
  | PatExpr
  | PatType (Maybe Text)
  deriving (Eq, Show)

data Action
  = ActionExpr
  | ActionTemplate TemplateExpr
  deriving (Eq, Show)

data GenRef
  = GenLit Text
  | GenHole Text
  deriving (Eq, Show)

data TemplateExpr
  = TId [RawPolyTypeExpr]
  | TGen GenRef (Maybe [RawPolyTypeExpr]) (Maybe [TemplateAttrArg]) (Maybe [TemplateBinderArg])
  | TTermRef Text
  | TBox Text TemplateExpr
  | TLoop TemplateExpr
  | TComp TemplateExpr TemplateExpr
  | TTensor TemplateExpr TemplateExpr
  | THole Int
  | TVar Text
  deriving (Eq, Show)

data TemplateBinderArg
  = TBAExpr TemplateExpr
  | TBAMeta Text
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
