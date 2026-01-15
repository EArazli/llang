{-# LANGUAGE OverloadedStrings #-}
module Strat.Surface2.CoreEval
  ( CoreVal(..)
  , CoreEnv
  , evalCoreExpr
  ) where

import Strat.Surface2.Def
import Strat.Surface2.Engine (Ctx(..))
import Strat.Surface2.Pattern
import Strat.Surface2.Term
import Strat.Surface2.InterfaceInst
import Strat.Kernel.Presentation
import Strat.Kernel.Signature
import Strat.Kernel.Term
import Strat.Kernel.Syntax
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import Control.Monad (foldM)

data CoreVal
  = CVCore Term
  | CVSurf STerm
  | CVCtx Ctx
  | CVNat Int
  deriving (Eq, Show)

type CoreEnv = M.Map Text CoreVal

evalCoreExpr :: Presentation -> SurfaceDef -> InterfaceInstance -> CoreEnv -> CoreExpr -> Either Text CoreVal
evalCoreExpr pres surf iface env expr =
  case expr of
    CoreVar name ->
      case M.lookup name env of
        Just v -> Right v
        Nothing ->
          case lookupOpSlot name iface of
            Just op -> applyOp pres op []
            Nothing ->
              case M.lookup (Con2Name name) (sdCons surf) of
                Just decl ->
                  if null (conArgs decl)
                    then Right (CVSurf (SCon (Con2Name name) []))
                    else Left ("core var is constructor with arguments: " <> name)
                Nothing -> Left ("unknown core var: " <> name)
    CoreApp f args ->
      case lookupDefine f surf of
        Just def -> evalDefine pres surf iface env def args
        Nothing ->
          case lookupOpSlot f iface of
            Just op -> do
              args' <- mapM (evalCoreExpr pres surf iface env) args
              coreArgs <- mapM requireCore args'
              applyOp pres op coreArgs
            Nothing ->
              case M.lookup (Con2Name f) (sdCons surf) of
                Just decl -> do
                  args' <- mapM (evalCoreExpr pres surf iface env) args
                  surfArgs <- mapM requireSurf args'
                  if length surfArgs /= length (conArgs decl)
                    then Left ("constructor arity mismatch: " <> f)
                    else
                      if any (not . null . caBinders) (conArgs decl)
                        then Left ("constructor with binders not supported in core expr: " <> f)
                        else Right (CVSurf (SCon (Con2Name f) (map (SArg []) surfArgs)))
                Nothing -> Left ("unknown core function: " <> f)

evalDefine :: Presentation -> SurfaceDef -> InterfaceInstance -> CoreEnv -> Define -> [CoreExpr] -> Either Text CoreVal
evalDefine pres surf iface env def args = do
  args' <- mapM (evalCoreExpr pres surf iface env) args
  tryClauses args' (defClauses def)
  where
    tryClauses _ [] = Left ("no matching define clause for " <> defName def)
    tryClauses vals (cl:cls) =
      case matchDefine surf env vals cl of
        Left _ -> tryClauses vals cls
        Right env' -> evalCoreExpr pres surf iface env' (dcBody cl)

matchDefine :: SurfaceDef -> CoreEnv -> [CoreVal] -> DefineClause -> Either Text CoreEnv
matchDefine surf env vals clause =
  if length vals /= length (dcArgs clause)
    then Left "define arity mismatch"
    else do
      env1 <- foldM (matchArg surf) env (zip (dcArgs clause) vals)
      foldM (matchWhere surf) env1 (dcWhere clause)

matchArg :: SurfaceDef -> CoreEnv -> (DefinePat, CoreVal) -> Either Text CoreEnv
matchArg surf env (pat, val) =
  case pat of
    DPVar name -> Right (M.insert name val env)
    DPNat np ->
      case val of
        CVNat n -> bindNat env np n
        _ -> Left "define: expected nat"
    DPSurf p ->
      case val of
        CVSurf t ->
          case matchPTerm p t of
            Nothing -> Left "define: pattern mismatch"
            Just sub -> bindMatch env sub
        _ -> Left "define: expected surface term"
    DPCtx cp ->
      case val of
        CVCtx ctx -> bindCtxPat surf env cp ctx
        _ -> Left "define: expected context"

bindMatch :: CoreEnv -> MatchSubst -> Either Text CoreEnv
bindMatch env subst = do
  let envTerms = M.fromList [ (renderMVar mv, CVSurf (instantiate mv ms)) | (mv, ms) <- M.toList (msTerms subst) ]
  let envNats = M.fromList [ (k, CVNat v) | (k, v) <- M.toList (msNats subst) ]
  pure (M.union env (M.union envTerms envNats))
  where
    instantiate mv ms =
      let args = map Ix [0 .. msArity ms - 1]
      in case instantiateMeta ms args of
          Just tm -> tm
          Nothing -> SFree (renderMVar mv)
    renderMVar (MVar t) = t

bindNat :: CoreEnv -> NatPat -> Int -> Either Text CoreEnv
bindNat env np n =
  case np of
    NatZero -> if n == 0 then Right env else Left "define: nat mismatch"
    NatSucc name -> if n > 0 then Right (M.insert name (CVNat (n - 1)) env) else Left "define: nat mismatch"
    NatVar name -> Right (M.insert name (CVNat n) env)

bindCtxPat :: SurfaceDef -> CoreEnv -> CtxPat -> Ctx -> Either Text CoreEnv
bindCtxPat surf env pat ctx@(Ctx xs) =
  case pat of
    CtxEmpty -> if null xs then Right env else Left "define: ctx mismatch"
    CtxVar name -> Right (M.insert name (CVCtx ctx) env)
    CtxExtend name varName tyPat ->
      case xs of
        [] -> Left "define: ctx mismatch"
        _ ->
          let (Ctx prefix) = Ctx (init xs)
              ty = last xs
          in do
            env1 <- bindCtxPat surf env (CtxVar name) (Ctx prefix)
            env2 <- matchArg surf env1 (DPSurf tyPat, CVSurf ty)
            Right (M.insert varName (CVSurf ty) env2)

matchWhere :: SurfaceDef -> CoreEnv -> WhereClause -> Either Text CoreEnv
matchWhere surf env clause =
  case M.lookup (wcName clause) env of
    Just (CVCtx ctx) -> bindCtxPat surf env (wcPat clause) ctx
    _ -> Left "define: where expects context"

lookupDefine :: Text -> SurfaceDef -> Maybe Define
lookupDefine name surf = M.lookup (slotKey name) (sdDefines surf)

lookupOpSlot :: Text -> InterfaceInstance -> Maybe OpName
lookupOpSlot name iface = M.lookup (slotKey name) (iiOps iface)

slotKey :: Text -> Text
slotKey t =
  case reverse (T.splitOn "." t) of
    [] -> t
    (x:_) -> x

requireCore :: CoreVal -> Either Text Term
requireCore val =
  case val of
    CVCore t -> Right t
    _ -> Left "core evaluation: expected core term"

requireSurf :: CoreVal -> Either Text STerm
requireSurf val =
  case val of
    CVSurf t -> Right t
    _ -> Left "core evaluation: expected surface term"

applyOp :: Presentation -> OpName -> [Term] -> Either Text CoreVal
applyOp pres op args =
  case mkOp (presSig pres) op args of
    Left err -> Left (T.pack (show err))
    Right t -> Right (CVCore t)
