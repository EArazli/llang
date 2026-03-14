{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DuplicateRecordFields #-}
module Strat.Poly.Syntax
  ( ObjName(..)
  , ObjRef(..)
  , ProviderRef(..)
  , ModuleValueRef(..)
  , mkModeMetaVar
  , identityModExpr
  , TmVar(..)
  , tmVarOwner
  , sameTmVarId
  , TermDiagram(..)
  , CodeArg(..)
  , CodeTerm(CTMeta, CTCon, CTLift)
  , Obj(..)
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
import Strat.Common.ModuleRef (ModuleValueRef(..))
import Strat.Common.Provider (ProviderRef(..))
import Strat.Poly.Literal (Literal)
import Strat.Poly.ModeSyntax (ModeName, ModExpr(..))
import Strat.Poly.Names (BoxName, GenName)


newtype ObjName = ObjName Text deriving (Eq, Ord, Read, Show)

data ObjRef = ObjRef
  { orMode :: ModeName
  , orName :: ObjName
  } deriving (Eq, Ord, Read, Show)

data TmVar = TmVar
  { tmvName :: Text
  , tmvSort :: Obj
  , tmvScope :: Int
  , tmvOwnerMode :: Maybe ModeName
  } deriving (Read, Show)

newtype PortId = PortId Int deriving (Eq, Ord, Read, Show)
newtype EdgeId = EdgeId Int deriving (Eq, Ord, Read, Show)
newtype BinderMetaVar = BinderMetaVar Text deriving (Eq, Ord, Read, Show)

data BinderArg
  = BAConcrete Diagram
  | BAMeta BinderMetaVar
  deriving (Eq, Ord, Read, Show)

data EdgePayload
  = PGen GenName [CodeArg] [BinderArg]
  | PProvider ProviderRef
  | PModuleRef ModuleValueRef
  | PBox BoxName Diagram
  | PFeedback Diagram
  | PSplice BinderMetaVar ModExpr
  | PTmMeta TmVar
  | PTmLit Literal
  | PInternalDrop
  deriving (Eq, Ord, Read, Show)

data Edge = Edge
  { eId :: EdgeId
  , ePayload :: EdgePayload
  , eIns :: [PortId]
  , eOuts :: [PortId]
  } deriving (Eq, Ord, Read, Show)

data Diagram = Diagram
  { dMode :: ModeName
  , dTmCtx :: [Obj]
  , dIn :: [PortId]
  , dOut :: [PortId]
  , dPortObj :: IM.IntMap Obj
  , dPortLabel :: IM.IntMap (Maybe Text)
  , dProd :: IM.IntMap (Maybe EdgeId)
  , dCons :: IM.IntMap (Maybe EdgeId)
  , dEdges :: IM.IntMap Edge
  , dNextPort :: Int
  , dNextEdge :: Int
  } deriving (Eq, Ord, Read, Show)

newtype TermDiagram = TermDiagram { unTerm :: Diagram }
  deriving (Eq, Ord, Read, Show)

data CodeArg
  = CAObj Obj
  | CATm TermDiagram
  deriving (Eq, Ord, Read, Show)

data CodeTerm
  = CTMeta TmVar
  | CTCon ObjRef [CodeArg]
  | CTLift ModExpr CodeTerm
  deriving (Eq, Ord, Read, Show)

data Obj = Obj
  { objOwnerMode :: ModeName
  , objCode :: CodeTerm
  }
  deriving (Eq, Ord, Read, Show)

metaSortObj :: ModeName -> Obj
metaSortObj mode =
  Obj
    { objOwnerMode = mode
    , objCode = CTCon (ObjRef mode (ObjName "__obj_meta_sort")) []
    }

mkModeMetaVar :: Text -> ModeName -> TmVar
mkModeMetaVar name mode =
  TmVar
    { tmvName = name
    , tmvSort = metaSortObj mode
    , tmvScope = 0
    , tmvOwnerMode = Just mode
    }

identityModExpr :: ModeName -> ModExpr
identityModExpr mode =
  ModExpr
    { meSrc = mode
    , meTgt = mode
    , mePath = []
    }

tmVarOwner :: TmVar -> ModeName
tmVarOwner TmVar { tmvOwnerMode = ownerM, tmvSort = sortTy } =
  case ownerM of
    Just owner -> owner
    Nothing -> objOwnerMode sortTy

tmVarIdKey :: TmVar -> (ModeName, Text, Int)
tmVarIdKey v =
  (tmVarOwner v, tmvName v, tmvScope v)

instance Eq TmVar where
  a == b = tmVarIdKey a == tmVarIdKey b

instance Ord TmVar where
  compare a b = compare (tmVarIdKey a) (tmVarIdKey b)

sameTmVarId :: TmVar -> TmVar -> Bool
sameTmVarId v w = tmVarIdKey v == tmVarIdKey w

type Context = [Obj]

newtype CanonDiagram = CanonDiagram { unCanon :: Diagram }
  deriving (Eq, Ord, Read, Show)

unPortId :: PortId -> Int
unPortId (PortId x) = x

unEdgeId :: EdgeId -> Int
unEdgeId (EdgeId x) = x
