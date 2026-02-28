{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
module Strat.Poly.Syntax
  ( ObjName(..)
  , ObjRef(..)
  , TyMeta(..)
  , ObjVar
  , pattern ObjVar
  , ovName
  , ovMode
  , ovSort
  , ovScope
  , ovOwnerMode
  , objVarToTmVar
  , tmVarToObjVar
  , TmFunName(..)
  , TmVar(..)
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
import Strat.Poly.Attr (AttrMap)
import Strat.Poly.ModeSyntax (ModeName, ModExpr)
import Strat.Poly.Names (BoxName, GenName)


newtype ObjName = ObjName Text deriving (Eq, Ord, Show)

data ObjRef = ObjRef
  { orMode :: ModeName
  , orName :: ObjName
  } deriving (Eq, Ord, Show)

data TyMeta = TyMeta
  { tmvName :: Text
  , tmvSort :: Obj
  , tmvScope :: Int
  , tmvOwnerMode :: Maybe ModeName
  } deriving (Show)

type ObjVar = TyMeta

newtype TmFunName = TmFunName Text deriving (Eq, Ord, Show)

data TmVar = TmVar
  { tmvName :: Text
  , tmvSort :: Obj
  , tmvScope :: Int
  , tmvOwnerMode :: Maybe ModeName
  } deriving (Show)

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
  } deriving (Eq, Ord, Show)

newtype TermDiagram = TermDiagram { unTerm :: Diagram }
  deriving (Eq, Ord, Show)

data CodeArg
  = CAObj Obj
  | CATm TermDiagram
  deriving (Eq, Ord, Show)

data CodeTerm
  = CTMeta TyMeta
  | CTCon ObjRef [CodeArg]
  | CTLift ModExpr CodeTerm
  deriving (Eq, Ord, Show)

data Obj = Obj
  { objOwnerMode :: ModeName
  , objCode :: CodeTerm
  }
  deriving (Eq, Ord, Show)

metaSortObj :: ModeName -> Obj
metaSortObj mode =
  Obj
    { objOwnerMode = mode
    , objCode = CTCon (ObjRef mode (ObjName "__obj_meta_sort")) []
    }

tmVarOwner :: TmVar -> ModeName
tmVarOwner TmVar { tmvOwnerMode = ownerM, tmvSort = sortTy } =
  case ownerM of
    Just owner -> owner
    Nothing -> objOwnerMode sortTy

tyMetaIdKey :: TyMeta -> (Text, Int)
tyMetaIdKey TyMeta { tmvName = name, tmvScope = scope } =
  (name, scope)

tmVarIdKey :: TmVar -> (Text, Int)
tmVarIdKey TmVar { tmvName = name, tmvScope = scope } =
  (name, scope)

instance Eq TyMeta where
  a == b = tyMetaIdKey a == tyMetaIdKey b

instance Ord TyMeta where
  compare a b = compare (tyMetaIdKey a) (tyMetaIdKey b)

instance Eq TmVar where
  a == b = tmVarIdKey a == tmVarIdKey b

instance Ord TmVar where
  compare a b = compare (tmVarIdKey a) (tmVarIdKey b)

sameTmVarId :: TmVar -> TmVar -> Bool
sameTmVarId v w = tmVarIdKey v == tmVarIdKey w

objVarToTmVar :: ObjVar -> TmVar
objVarToTmVar v@TyMeta { tmvName = name, tmvSort = sortTy, tmvScope = scope } =
  TmVar
    { tmvName = name
    , tmvSort = sortTy
    , tmvScope = scope
    , tmvOwnerMode = Just (ovOwnerMode v)
    }

tmVarToObjVar :: TmVar -> ObjVar
tmVarToObjVar v@TmVar { tmvName = name, tmvSort = sortTy, tmvScope = scope } =
  TyMeta
    { tmvName = name
    , tmvSort = sortTy
    , tmvScope = scope
    , tmvOwnerMode = Just (tmVarOwner v)
    }

ovSort :: ObjVar -> Obj
ovSort TyMeta { tmvSort = sortTy } = sortTy

ovScope :: ObjVar -> Int
ovScope TyMeta { tmvScope = scope } = scope

ovOwnerMode :: ObjVar -> ModeName
ovOwnerMode TyMeta { tmvOwnerMode = Just owner } = owner
ovOwnerMode TyMeta { tmvName = name } =
  error
    ( "ObjVar invariant violated: missing owner mode for type metavariable "
        <> show name
    )

objVarOwner :: ObjVar -> ModeName
objVarOwner = ovOwnerMode

objVarView :: ObjVar -> Maybe (Text, ModeName)
objVarView v@TyMeta { tmvName = name } = Just (name, objVarOwner v)

pattern ObjVar :: Text -> ModeName -> ObjVar
pattern ObjVar {ovName, ovMode} <- (objVarView -> Just (ovName, ovMode))
  where
    ObjVar ovName ovMode =
      TyMeta
        { tmvName = ovName
        , tmvSort = metaSortObj ovMode
        , tmvScope = 0
        , tmvOwnerMode = Just ovMode
        }

{-# COMPLETE ObjVar #-}

type Context = [Obj]

newtype CanonDiagram = CanonDiagram { unCanon :: Diagram }
  deriving (Eq, Ord, Show)

unPortId :: PortId -> Int
unPortId (PortId x) = x

unEdgeId :: EdgeId -> Int
unEdgeId (EdgeId x) = x
