{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Syntax
  ( TypeName(..)
  , TypeRef(..)
  , TyVar(..)
  , TmFunName(..)
  , TmVar(..)
  , TermDiagram(..)
  , TypeArg(..)
  , TypeExpr(..)
  , Context
  , PortId(..)
  , EdgeId(..)
  , unPortId
  , unEdgeId
  , BinderMetaVar(..)
  , BinderArg(..)
  , EdgePayload(..)
  , Edge(..)
  , Diagram(..)
  , CanonDiagram(..)
  ) where

import Data.Text (Text)
import qualified Data.IntMap.Strict as IM
import Strat.Poly.Attr (AttrMap)
import Strat.Poly.ModeTheory (ModeName, ModExpr)
import Strat.Poly.Names (BoxName, GenName)


newtype TypeName = TypeName Text deriving (Eq, Ord, Show)

data TypeRef = TypeRef
  { trMode :: ModeName
  , trName :: TypeName
  } deriving (Eq, Ord, Show)

data TyVar = TyVar
  { tvName :: Text
  , tvMode :: ModeName
  } deriving (Eq, Ord, Show)

newtype TmFunName = TmFunName Text deriving (Eq, Ord, Show)

data TmVar = TmVar
  { tmvName :: Text
  , tmvSort :: TypeExpr
  , tmvScope :: Int
  } deriving (Eq, Ord, Show)

newtype PortId = PortId Int deriving (Eq, Ord, Show)
newtype EdgeId = EdgeId Int deriving (Eq, Ord, Show)
newtype BinderMetaVar = BinderMetaVar Text deriving (Eq, Ord, Show)

data BinderArg
  = BAConcrete Diagram
  | BAMeta BinderMetaVar
  deriving (Eq, Ord, Show)

data EdgePayload
  = PGen GenName AttrMap [BinderArg]
  | PBox BoxName Diagram
  | PFeedback Diagram
  | PSplice BinderMetaVar
  | PTmMeta TmVar
  | PInternalDrop
  deriving (Eq, Ord, Show)

data Edge = Edge
  { eId :: EdgeId
  , ePayload :: EdgePayload
  , eIns :: [PortId]
  , eOuts :: [PortId]
  } deriving (Eq, Ord, Show)

data Diagram = Diagram
  { dMode :: ModeName
  , dTmCtx :: [TypeExpr]
  , dIn :: [PortId]
  , dOut :: [PortId]
  , dPortTy :: IM.IntMap TypeExpr
  , dPortLabel :: IM.IntMap (Maybe Text)
  , dProd :: IM.IntMap (Maybe EdgeId)
  , dCons :: IM.IntMap (Maybe EdgeId)
  , dEdges :: IM.IntMap Edge
  , dNextPort :: Int
  , dNextEdge :: Int
  } deriving (Eq, Ord, Show)

newtype TermDiagram = TermDiagram { unTerm :: Diagram }
  deriving (Eq, Ord, Show)

data TypeArg
  = TAType TypeExpr
  | TATm TermDiagram
  deriving (Eq, Ord, Show)

data TypeExpr
  = TVar TyVar
  | TCon TypeRef [TypeArg]
  | TMod ModExpr TypeExpr
  deriving (Eq, Ord, Show)

type Context = [TypeExpr]

newtype CanonDiagram = CanonDiagram { unCanon :: Diagram }
  deriving (Eq, Ord, Show)

unPortId :: PortId -> Int
unPortId (PortId x) = x

unEdgeId :: EdgeId -> Int
unEdgeId (EdgeId x) = x
