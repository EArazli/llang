{-# LANGUAGE OverloadedStrings #-}
module Strat.Backend.Models
  ( symbolicModel
  , natModel
  , stringMonoidModel
  ) where

import Strat.Backend
import Strat.Kernel.Syntax
import qualified Data.Text as T

symbolicModel :: Model
symbolicModel =
  Model
    { interpOp = \op args ->
        if null args
          then Right (VAtom (renderOp op))
          else Right (VList (VAtom (renderOp op) : args))
    , interpSort = \s -> Right (SortValue (renderSort s))
    }

natModel :: Model
natModel =
  Model
    { interpOp = \op args ->
        case (unqualify op, args) of
          ("Z", []) -> Right (VInt 0)
          ("S", [VInt n]) -> Right (VInt (n + 1))
          ("add", [VInt a, VInt b]) -> Right (VInt (a + b))
          ("mul", [VInt a, VInt b]) -> Right (VInt (a * b))
          (name, []) -> Left (RuntimeError ("unknown Nat op: " <> name))
          (name, _) -> Left (RuntimeError ("bad args for Nat op: " <> name))
    , interpSort = \s -> Right (SortValue (renderSort s))
    }

stringMonoidModel :: Model
stringMonoidModel =
  Model
    { interpOp = \op args ->
        case (unqualify op, args) of
          ("e", []) -> Right (VString "")
          ("m", [VString a, VString b]) -> Right (VString (a <> b))
          ("k", [v]) -> Right v
          (name, []) -> Right (VString name)
          (name, _) -> Left (RuntimeError ("bad args for monoid op: " <> name))
    , interpSort = \s -> Right (SortValue (renderSort s))
    }

renderOp :: OpName -> T.Text
renderOp (OpName t) = t

renderSort :: Sort -> T.Text
renderSort (Sort (SortName name) _) = name

unqualify :: OpName -> T.Text
unqualify (OpName t) =
  case T.splitOn "." t of
    [] -> t
    parts -> last parts
