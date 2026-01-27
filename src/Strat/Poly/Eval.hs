{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Eval
  ( evalDiagram
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import Strat.Backend (Value(..), RuntimeError(..))
import Strat.Model.Spec (ModelSpec(..), OpClause(..), DefaultBehavior(..), MExpr(..))
import Strat.Poly.Doctrine
import Strat.Poly.Diagram
import Strat.Poly.Graph (Edge(..), EdgePayload(..), PortId)
import Strat.Poly.Names (GenName(..))
import Strat.Poly.ModeTheory (ModeName)


data PolyModel = PolyModel
  { pmInterp :: GenName -> [Value] -> Either Text Value
  , pmDefault :: DefaultBehavior
  }

instantiatePolyModel :: ModelSpec -> PolyModel
instantiatePolyModel spec =
  let clauseMap = M.fromList [ (ocOp c, mkClause c) | c <- msClauses spec ]
  in PolyModel
      { pmInterp = \(GenName name) args ->
          case M.lookup name clauseMap of
            Just f -> f args
            Nothing -> defaultInterp (msDefault spec) name args
      , pmDefault = msDefault spec
      }
  where
    mkClause clause args =
      let env = M.fromList (zip (ocArgs clause) args)
      in mapError (evalExpr env (ocExpr clause))
    mapError res =
      case res of
        Left (RuntimeError msg) -> Left msg
        Right v -> Right v

defaultInterp :: DefaultBehavior -> Text -> [Value] -> Either Text Value
defaultInterp behavior op args =
  case behavior of
    DefaultSymbolic ->
      if null args
        then Right (VAtom op)
        else Right (VList (VAtom op : args))
    DefaultError msg -> Left msg

-- Evaluation

evalDiagram :: Doctrine -> ModelSpec -> Diagram -> [Value] -> Either Text [Value]
evalDiagram doc spec diag inputs =
  evalDiagramWithModel (instantiatePolyModel spec) doc diag inputs

evalDiagramWithModel :: PolyModel -> Doctrine -> Diagram -> [Value] -> Either Text [Value]
evalDiagramWithModel model doc diag inputs = do
  if length inputs /= length (dIn diag)
    then Left "poly eval: input arity mismatch"
    else do
      let env0 = M.fromList (zip (dIn diag) inputs)
      env <- evalEdges model doc (dMode diag) env0 (IM.toAscList (dEdges diag))
      mapM (lookupPort env) (dOut diag)
  where
    lookupPort env pid =
      case M.lookup pid env of
        Nothing -> Left "poly eval: missing output value"
        Just v -> Right v


evalEdges :: PolyModel -> Doctrine -> ModeName -> M.Map PortId Value -> [(Int, Edge)] -> Either Text (M.Map PortId Value)
evalEdges _ _ _ env [] = Right env
evalEdges model doc mode env edges =
  case readyPartition env edges of
    ([], _) -> Left "poly eval: diagram has cycle or missing inputs"
    (ready, rest) -> do
      env' <- foldl step (Right env) ready
      evalEdges model doc mode env' rest
  where
    step acc (_, edge) = do
      env' <- acc
      args <- mapM (lookupPort env') (eIns edge)
      outs <- case ePayload edge of
        PGen name -> evalGen model doc mode name args
        PBox _ inner -> evalDiagramWithModel model doc inner args
      if length outs /= length (eOuts edge)
        then Left "poly eval: output arity mismatch"
        else assignOutputs env' (zip (eOuts edge) outs)
    lookupPort env' pid =
      case M.lookup pid env' of
        Nothing -> Left "poly eval: missing input value"
        Just v -> Right v
    assignOutputs env' pairs =
      foldl assign (Right env') pairs
    assign acc (pid, val) = do
      mp <- acc
      case M.lookup pid mp of
        Just _ -> Left "poly eval: output already assigned"
        Nothing -> Right (M.insert pid val mp)
    readyPartition env' =
      foldr
        (\e (rs, ns) -> if all (`M.member` env') (eIns (snd e)) then (e:rs, ns) else (rs, e:ns))
        ([], [])


evalGen :: PolyModel -> Doctrine -> ModeName -> GenName -> [Value] -> Either Text [Value]
evalGen model doc mode name args
  | name == GenName "dup" =
      case args of
        [v] -> Right [v, v]
        _ -> Left "poly eval: dup expects one input"
  | name == GenName "drop" =
      case args of
        [_] -> Right []
        _ -> Left "poly eval: drop expects one input"
  | name == GenName "swap" =
      case args of
        [a, b] -> Right [b, a]
        _ -> Left "poly eval: swap expects two inputs"
  | otherwise = do
      gen <- lookupGen doc mode name
      let codLen = length (gdCod gen)
      val <- pmInterp model name args
      if codLen == 1
        then Right [val]
        else case val of
          VList xs | length xs == codLen -> Right xs
          _ -> Left "poly eval: expected list output"

lookupGen :: Doctrine -> ModeName -> GenName -> Either Text GenDecl
lookupGen doc mode name =
  case M.lookup mode (dGens doc) >>= M.lookup name of
    Nothing -> Left "poly eval: unknown generator"
    Just gd -> Right gd

-- Expression eval (copied from Model.Spec)

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
    "++" -> binString (<>)
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
