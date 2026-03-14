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
  , TemplateGenArg(..)
  , TemplateArgExpr(..)
  , TemplateBinderArg(..)
  ) where

import Data.Text (Text)
import Strat.Poly.ModeTheory (ModeName)
import Strat.Poly.DSL.AST (RawPolyObjExpr)

data PolySurfaceDef = PolySurfaceDef
  { psName :: Text
  , psDoctrine :: Text
  , psBaseDoctrine :: Maybe Text
  , psMode :: ModeName
  , psSpec :: SurfaceSpec
  } deriving (Eq, Read, Show)

data SurfaceSpec = SurfaceSpec
  { ssName :: Text
  , ssDoctrine :: Text
  , ssBaseDoctrine :: Maybe Text
  , ssMode :: Text
  , ssLexer :: Maybe LexerSpec
  , ssExprSpec :: Maybe ExprSpec
  } deriving (Eq, Read, Show)

data LexerSpec = LexerSpec
  { lsKeywords :: [Text]
  , lsSymbols :: [Text]
  } deriving (Eq, Read, Show)

data ExprSpec = ExprSpec
  { esAtoms :: [ExprRule]
  , esPrefixes :: [ExprRule]
  , esInfixes :: [InfixRule]
  , esApp :: Maybe AppRule
  } deriving (Eq, Read, Show)

data ExprRule = ExprRule
  { erPattern :: [PatItem]
  , erAction :: Action
  , erBinder :: Maybe BinderDecl
  } deriving (Eq, Read, Show)

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
  deriving (Eq, Read, Show)

data InfixAssoc = AssocL | AssocR
  deriving (Eq, Read, Show)

data InfixRule = InfixRule
  { irAssoc :: InfixAssoc
  , irPrec :: Int
  , irToken :: Text
  , irAction :: Action
  } deriving (Eq, Read, Show)

newtype AppRule = AppRule
  { arAction :: Action
  } deriving (Eq, Read, Show)

data PatItem
  = PatLit Text
  | PatIdent (Maybe Text)
  | PatInt (Maybe Text)
  | PatString (Maybe Text)
  | PatBool (Maybe Text)
  | PatExpr
  | PatType (Maybe Text)
  deriving (Eq, Read, Show)

data Action
  = ActionExpr
  | ActionTemplate TemplateExpr
  deriving (Eq, Read, Show)

data GenRef
  = GenLit Text
  | GenHole Text
  deriving (Eq, Read, Show)

data TemplateExpr
  = TId [RawPolyObjExpr]
  | TGen GenRef (Maybe [TemplateGenArg]) (Maybe [TemplateBinderArg])
  | TBox Text TemplateExpr
  | TTrace Int TemplateExpr
  | TLoop TemplateExpr
  | TComp TemplateExpr TemplateExpr
  | TTensor TemplateExpr TemplateExpr
  | THole Int
  | OVar Text
  deriving (Eq, Read, Show)

data TemplateBinderArg
  = TBAExpr TemplateExpr
  | TBAMeta Text
  deriving (Eq, Read, Show)

data TemplateGenArg
  = TGNamed Text TemplateArgExpr
  | TGPos TemplateArgExpr
  deriving (Eq, Read, Show)

data TemplateArgExpr
  = TAHole Text
  | TAExpr RawPolyObjExpr
  deriving (Eq, Read, Show)
