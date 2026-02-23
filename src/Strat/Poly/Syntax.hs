{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
module Strat.Poly.Syntax
  ( ObjName(..)
  , ObjRef(..)
  , ObjVar
  , pattern ObjVar
  , ovName
  , ovMode
  , TmFunName(..)
  , TmVar(..)
  , TermDiagram(..)
  , CodeArg(..)
  , CodeTerm(CTMeta, CTCon, CTMod)
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

type ObjVar = TmVar

newtype TmFunName = TmFunName Text deriving (Eq, Ord, Show)

data TmVar = TmVar
  { tmvName :: Text
  , tmvSort :: Obj
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
  = CTMeta TmVar
  | CTCon ObjRef [CodeArg]
  | CTMod ModExpr CodeTerm
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

pattern ObjVar :: Text -> ModeName -> ObjVar
pattern ObjVar {ovName, ovMode} <- TmVar ovName (objOwnerMode -> ovMode) _
  where
    ObjVar ovName ovMode =
      TmVar
        { tmvName = ovName
        , tmvSort = metaSortObj ovMode
        , tmvScope = 0
        }

{-# COMPLETE ObjVar #-}

type Context = [Obj]

newtype CanonDiagram = CanonDiagram { unCanon :: Diagram }
  deriving (Eq, Ord, Show)

unPortId :: PortId -> Int
unPortId (PortId x) = x

unEdgeId :: EdgeId -> Int
unEdgeId (EdgeId x) = x
