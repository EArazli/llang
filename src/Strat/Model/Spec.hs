{-# LANGUAGE OverloadedStrings #-}
module Strat.Model.Spec
  ( ModelSpec(..)
  , OpClause(..)
  , DefaultBehavior(..)
  , MExpr(..)
  , instantiateModel
  ) where

import Strat.Backend (Model(..), Value(..), SortValue(..), RuntimeError(..))
import Strat.Kernel.Presentation (Presentation(..))
import Strat.Kernel.Signature (Signature(..), OpDecl(..))
import Strat.Kernel.Syntax (OpName(..), Sort(..), SortName(..))
import Strat.Frontend.Resolve (resolveOpText)
import Data.Text (Text)
import qualified Data.Map.Strict as M


data ModelSpec = ModelSpec
  { msName    :: Text
  , msClauses :: [OpClause]
  , msDefault :: DefaultBehavior
  }
  deriving (Eq, Show)


data OpClause = OpClause
  { ocOp   :: Text
  , ocArgs :: [Text]
  , ocExpr :: MExpr
  }
  deriving (Eq, Show)


data DefaultBehavior
  = DefaultSymbolic
  | DefaultError Text
  deriving (Eq, Show)


data MExpr
  = MVar Text
  | MInt Int
  | MString Text
  | MBool Bool
  | MList [MExpr]
  | MIf MExpr MExpr MExpr
  | MBinOp Text MExpr MExpr
  deriving (Eq, Show)

instantiateModel :: Presentation -> [Text] -> ModelSpec -> Either Text Model
instantiateModel pres opens spec = do
  clauses <- mapM resolveClause (msClauses spec)
  let clauseMap = M.fromList clauses
  pure Model
    { interpOp = \op args ->
        case M.lookup op clauseMap of
          Just f -> f args
          Nothing -> defaultInterp (msDefault spec) op args
    , interpSort = \(Sort (SortName name) _) -> Right (SortValue name)
    }
  where
    sig = presSig pres

    resolveClause :: OpClause -> Either Text (OpName, [Value] -> Either RuntimeError Value)
    resolveClause clause = do
      op <- resolveOpText sig opens (ocOp clause)
      let arity = opArity sig op
      if arity /= length (ocArgs clause)
        then Left ("Arity mismatch for model op " <> ocOp clause)
        else do
          let f args = evalExpr (M.fromList (zip (ocArgs clause) args)) (ocExpr clause)
          pure (op, f)

opArity :: Signature -> OpName -> Int
opArity sig op =
  case M.lookup op (sigOps sig) of
    Nothing -> 0
    Just decl -> length (opTele decl)


defaultInterp :: DefaultBehavior -> OpName -> [Value] -> Either RuntimeError Value
defaultInterp behavior op args =
  case behavior of
    DefaultSymbolic ->
      if null args
        then Right (VAtom (renderOp op))
        else Right (VList (VAtom (renderOp op) : args))
    DefaultError msg -> Left (RuntimeError msg)

renderOp :: OpName -> Text
renderOp (OpName t) = t


evalExpr :: M.Map Text Value -> MExpr -> Either RuntimeError Value
evalExpr env expr =
  case expr of
    MVar name ->
      case M.lookup name env of
        Just v -> Right v
        Nothing -> Left (RuntimeError ("unknown variable: " <> name))
    MInt n -> Right (VInt n)
    MString s -> Right (VString s)
    MBool b -> Right (VBool b)
    MList xs -> VList <$> mapM (evalExpr env) xs
    MIf c t e -> do
      cv <- evalExpr env c
      case cv of
        VBool True -> evalExpr env t
        VBool False -> evalExpr env e
        _ -> Left (RuntimeError "if condition must be bool")
    MBinOp op a b -> do
      av <- evalExpr env a
      bv <- evalExpr env b
      evalBinOp op av bv


evalBinOp :: Text -> Value -> Value -> Either RuntimeError Value
evalBinOp op a b =
  case op of
    "+" -> binInt (+)
    "*" -> binInt (*)
    "++" -> binString (<> )
    "==" -> Right (VBool (a == b))
    _ -> Left (RuntimeError ("unknown operator: " <> op))
  where
    binInt f =
      case (a, b) of
        (VInt x, VInt y) -> Right (VInt (f x y))
        _ -> Left (RuntimeError "expected int operands")
    binString f =
      case (a, b) of
        (VString x, VString y) -> Right (VString (f x y))
        _ -> Left (RuntimeError "expected string operands")
