{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Eval
  ( evalDiagram
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import qualified Data.List as L
import qualified Data.Graph as G
import Strat.Backend (Value(..), RuntimeError(..))
import Strat.Model.Spec (ModelSpec(..), OpClause(..), DefaultBehavior(..), MExpr(..))
import Strat.Poly.Doctrine
import Strat.Poly.Diagram
import Strat.Poly.Graph (Edge(..), EdgePayload(..), PortId(..), EdgeId(..))
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
      let comps = sccOrder diag
      (envFinal, bindings) <- evalSCCs model doc (dMode diag) env0 M.empty comps
      outputs <- mapM (lookupPort envFinal) (dOut diag)
      if M.null bindings
        then Right outputs
        else do
          let bindingList = renderBindings bindings
          let wrap v = VList [VAtom "letrec", bindingList, v]
          Right (map wrap outputs)
  where
    lookupPort env pid =
      case M.lookup pid env of
        Nothing -> Left "poly eval: missing output value"
        Just v -> Right v


evalSCCs :: PolyModel -> Doctrine -> ModeName -> M.Map PortId Value -> M.Map PortId Value -> [G.SCC Edge] -> Either Text (M.Map PortId Value, M.Map PortId Value)
evalSCCs _ _ _ env bindings [] = Right (env, bindings)
evalSCCs model doc mode env bindings (comp:rest) =
  case comp of
    G.AcyclicSCC edge -> do
      env' <- evalAcyclicEdge model doc mode env edge
      evalSCCs model doc mode env' bindings rest
    G.CyclicSCC edges -> do
      (env', bindings') <- evalCyclic model doc mode env bindings edges
      evalSCCs model doc mode env' bindings' rest

evalAcyclicEdge :: PolyModel -> Doctrine -> ModeName -> M.Map PortId Value -> Edge -> Either Text (M.Map PortId Value)
evalAcyclicEdge model doc mode env edge = do
  args <- mapM (lookupPort env) (eIns edge)
  outs <- case ePayload edge of
    PGen name -> evalGen model doc mode name args
    PBox _ inner -> evalDiagramWithModel model doc inner args
  if length outs /= length (eOuts edge)
    then Left "poly eval: output arity mismatch"
    else assignOutputs env (zip (eOuts edge) outs)
  where
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

evalCyclic :: PolyModel -> Doctrine -> ModeName -> M.Map PortId Value -> M.Map PortId Value -> [Edge] -> Either Text (M.Map PortId Value, M.Map PortId Value)
evalCyclic model doc mode env bindings edges = do
  let producedPorts = concatMap eOuts edges
  env' <- foldl assignPlaceholder (Right env) producedPorts
  bindings' <- foldl (computeEdge env') (Right bindings) (sortEdges edges)
  pure (env', bindings')
  where
    assignPlaceholder acc pid = do
      mp <- acc
      let var = portVar pid
      Right (M.insert pid (VAtom var) mp)

    computeEdge env' acc edge = do
      binds <- acc
      args <- mapM (lookupPort env') (eIns edge)
      outs <- case ePayload edge of
        PGen name -> evalGenSymbolic model doc mode name args
        PBox _ inner -> evalDiagramWithModel model doc inner args
      if length outs /= length (eOuts edge)
        then Left "poly eval: output arity mismatch"
        else do
          let binds' = foldl addBind binds (zip (eOuts edge) outs)
          Right binds'

    lookupPort env' pid =
      case M.lookup pid env' of
        Nothing -> Left "poly eval: missing input value"
        Just v -> Right v

    addBind mp (pid, val) = M.insert pid val mp

evalGenSymbolic :: PolyModel -> Doctrine -> ModeName -> GenName -> [Value] -> Either Text [Value]
evalGenSymbolic model doc mode name args = do
  gen <- lookupGen doc mode name
  let codLen = length (gdCod gen)
  case pmInterp model name args of
    Right val ->
      if codLen == 1
        then Right [val]
        else case val of
          VList xs | length xs == codLen -> Right xs
          _ -> Left "poly eval: expected list output"
    Left _ ->
      Right [VList [VAtom (renderGen name <> "#" <> T.pack (show i)), VList args] | i <- [0 .. codLen - 1]]

renderGen :: GenName -> Text
renderGen (GenName t) = t

renderBindings :: M.Map PortId Value -> Value
renderBindings bindings =
  let pairs = [ (pid, val) | (pid, val) <- M.toList bindings ]
      sorted = L.sortOn (\(PortId k, _) -> k) pairs
      toBinding (pid, val) = VList [VAtom (portVar pid), val]
  in VList (map toBinding sorted)

portVar :: PortId -> Text
portVar (PortId k) = "$p" <> T.pack (show k)

sortEdges :: [Edge] -> [Edge]
sortEdges = L.sortOn (\e -> edgeKey (eId e))
  where
    edgeKey (EdgeId k) = k

sccOrder :: Diagram -> [G.SCC Edge]
sccOrder diag =
  reverse
    (G.stronglyConnComp
      [ (edge, eId edge, outgoing edge)
      | edge <- IM.elems (dEdges diag)
      ])
  where
    outgoing edge =
      [ eid
      | p <- eOuts edge
      , Just (Just eid) <- [IM.lookup (portKey p) (dCons diag)]
      ]
    portKey (PortId k) = k


evalGen :: PolyModel -> Doctrine -> ModeName -> GenName -> [Value] -> Either Text [Value]
evalGen model doc mode name args = do
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
