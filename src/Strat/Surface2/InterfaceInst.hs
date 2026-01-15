{-# LANGUAGE OverloadedStrings #-}
module Strat.Surface2.InterfaceInst
  ( InterfaceInstance(..)
  , instantiateInterface
  ) where

import Strat.Surface2.Interface
import Strat.Kernel.Presentation
import Strat.Kernel.Signature
import Strat.Kernel.Syntax
import Strat.Frontend.Resolve (resolveOpText, resolveSortText)
import Data.Text (Text)
import qualified Data.Map.Strict as M

data InterfaceInstance = InterfaceInstance
  { iiKind :: InterfaceKind
  , iiOps :: M.Map Text OpName
  , iiSorts :: M.Map Text SortName
  } deriving (Eq, Show)

instantiateInterface :: Presentation -> [Text] -> InterfaceSpec -> InterfaceKind -> Either Text InterfaceInstance
instantiateInterface pres opens spec kind = do
  let sig = presSig pres
  let slots = M.toList (ikSlots kind)
  ops <- mapM (resolveSlotOp sig opens) slots
  sorts <- mapM (resolveSlotSort sig opens) slots
  let sortMap = M.fromList [ (slot, sort) | (slot, Just sort) <- sorts ]
  validateHom sig sortMap
  pure InterfaceInstance
    { iiKind = kind
    , iiOps = M.fromList [ (slot, op) | (slot, Just op) <- ops ]
    , iiSorts = sortMap
    }
  where
    resolveSlotOp sig opens (slotKey, SlotOp _ arity) =
      case M.lookup slotKey (isSlots spec) of
        Nothing -> Left ("interface missing slot: " <> slotKey)
        Just target ->
          case resolveOpText sig opens target of
            Left _ -> Left ("unknown op in interface: " <> target)
            Right op ->
              case M.lookup op (sigOps sig) of
                Nothing -> Left ("unknown op in interface: " <> target)
                Just decl ->
                  if length (opTele decl) == arity
                    then Right (slotKey, Just op)
                    else Left ("arity mismatch for slot " <> slotKey)
    resolveSlotOp _ _ (slotKey, _) = Right (slotKey, Nothing)

    resolveSlotSort sig opens (slotKey, SlotSort _) =
      case M.lookup slotKey (isSlots spec) of
        Nothing -> Left ("interface missing slot: " <> slotKey)
        Just target ->
          case resolveSortText sig opens target of
            Left _ -> Left ("unknown sort in interface: " <> target)
            Right sn ->
              case M.lookup sn (sigSortCtors sig) of
                Nothing -> Left ("unknown sort in interface: " <> target)
                Just _ -> Right (slotKey, Just sn)
    resolveSlotSort _ _ (slotKey, _) = Right (slotKey, Nothing)

validateHom :: Signature -> M.Map Text SortName -> Either Text ()
validateHom sig sortMap =
  case (M.lookup "ObjSort" sortMap, M.lookup "HomSort" sortMap) of
    (Just obj, Just hom) ->
      case M.lookup hom (sigSortCtors sig) of
        Nothing -> Left "HomSort not found in signature"
        Just ctor ->
          if length (scParamSort ctor) /= 2
            then Left "HomSort must have two parameters"
            else if all (== Sort obj []) (scParamSort ctor)
              then Right ()
              else Left "HomSort parameters must be ObjSort"
    _ -> Right ()
