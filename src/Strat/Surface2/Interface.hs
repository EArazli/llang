{-# LANGUAGE OverloadedStrings #-}
module Strat.Surface2.Interface
  ( InterfaceSpec(..)
  , InterfaceKind(..)
  , InterfaceSlot(..)
  , builtinInterfaceKinds
  , lookupInterfaceKind
  ) where

import Strat.Kernel.DSL.AST (RawExpr)
import Data.Text (Text)
import qualified Data.Map.Strict as M

data InterfaceSpec = InterfaceSpec
  { isName :: Text
  , isDoctrine :: RawExpr
  , isSlots :: M.Map Text Text
  } deriving (Eq, Show)

data InterfaceSlot
  = SlotSort Text
  | SlotOp Text Int
  deriving (Eq, Show)

data InterfaceKind = InterfaceKind
  { ikName :: Text
  , ikSlots :: M.Map Text InterfaceSlot
  } deriving (Eq, Show)

builtinInterfaceKinds :: M.Map Text InterfaceKind
builtinInterfaceKinds =
  M.fromList
    [ ("CCC", InterfaceKind "CCC" cccSlots)
    , ("CCC_Bool", InterfaceKind "CCC_Bool" (cccSlots <> cccBoolSlots))
    ]
  where
    cccSlots =
      M.fromList
        [ ("ObjSort", SlotSort "Obj")
        , ("HomSort", SlotSort "Hom")
        , ("id", SlotOp "id" 1)
        , ("comp", SlotOp "comp" 5)
        , ("Unit", SlotOp "Unit" 0)
        , ("prod", SlotOp "prod" 2)
        , ("exl", SlotOp "exl" 2)
        , ("exr", SlotOp "exr" 2)
        , ("pair", SlotOp "pair" 5)
        , ("exp", SlotOp "exp" 2)
        , ("curry", SlotOp "curry" 4)
        , ("eval", SlotOp "eval" 2)
        ]
    cccBoolSlots =
      M.fromList
        [ ("terminal", SlotOp "terminal" 1)
        , ("Bool", SlotOp "Bool" 0)
        , ("T", SlotOp "T" 0)
        , ("F", SlotOp "F" 0)
        ]

lookupInterfaceKind :: Text -> Maybe InterfaceKind
lookupInterfaceKind name = M.lookup name builtinInterfaceKinds
