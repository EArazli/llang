{-# LANGUAGE OverloadedStrings #-}
module Strat.Backend
  ( Value(..)
  , SortValue(..)
  , RuntimeError(..)
  , Model(..)
  , evalTerm
  , evalTermWithEnv
  ) where

import Strat.Kernel.Syntax
import qualified Data.Map.Strict as M
import Data.Text (Text)

data Value
  = VAtom Text
  | VList [Value]
  deriving (Eq, Show)

data SortValue = SortValue Text
  deriving (Eq, Show)

data RuntimeError = RuntimeError Text
  deriving (Eq, Show)

data Model = Model
  { interpOp   :: OpName -> [Value] -> Either RuntimeError Value
  , interpSort :: Sort -> Either RuntimeError SortValue
  }

evalTerm :: Model -> Term -> Either RuntimeError Value
evalTerm model = evalTermWithEnv model M.empty

evalTermWithEnv :: Model -> M.Map Var Value -> Term -> Either RuntimeError Value
evalTermWithEnv model env tm =
  case termNode tm of
    TVar v ->
      case M.lookup v env of
        Just val -> Right val
        Nothing -> Left (RuntimeError "unbound variable")
    TOp op args -> do
      args' <- mapM (evalTermWithEnv model env) args
      interpOp model op args'
