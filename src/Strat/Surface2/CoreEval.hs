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
import Strat.Kernel.Presentation
import Strat.Kernel.Signature (sigOps)
import Strat.Kernel.Syntax
import Strat.Kernel.Morphism
import Strat.Kernel.Subst (applySubstSort)
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

type MorphismEnv = M.Map Text Morphism

evalCoreExpr :: Presentation -> SurfaceDef -> MorphismEnv -> CoreEnv -> CoreExpr -> Either Text CoreVal
evalCoreExpr pres surf morphs env expr =
  case expr of
    CoreVar name ->
      case M.lookup name env of
        Just v -> Right v
        Nothing ->
          case resolveOpInterp morphs name of
            Right interp ->
              if null (oiTele interp)
                then Right (CVCore (applyOpInterp interp []))
                else Left ("core var is op with arguments: " <> name)
            Left _ ->
              case M.lookup (Con2Name name) (sdCons surf) of
                Just decl ->
                  if null (conArgs decl)
                    then Right (CVSurf (SCon (Con2Name name) []))
                    else Left ("core var is constructor with arguments: " <> name)
                Nothing -> Left ("unknown core var: " <> name)
    CoreApp f args ->
      case lookupDefine f surf of
        Just def -> evalDefine pres surf morphs env def args
        Nothing ->
          case resolveOpInterp morphs f of
            Right interp -> do
              args' <- mapM (evalCoreExpr pres surf morphs env) args
              coreArgs <- mapM requireCore args'
              if length coreArgs /= length (oiTele interp)
                then Left ("core op arity mismatch: " <> f)
                else do
                  checkOpArgs f (oiTele interp) coreArgs
                  Right (CVCore (applyOpInterp interp coreArgs))
            Left _ ->
              case M.lookup (Con2Name f) (sdCons surf) of
                Just decl -> do
                  args' <- mapM (evalCoreExpr pres surf morphs env) args
                  surfArgs <- mapM requireSurf args'
                  if length surfArgs /= length (conArgs decl)
                    then Left ("constructor arity mismatch: " <> f)
                    else
                      if any (not . null . caBinders) (conArgs decl)
                        then Left ("constructor with binders not supported in core expr: " <> f)
                        else Right (CVSurf (SCon (Con2Name f) (map (SArg []) surfArgs)))
                Nothing -> Left ("unknown core function: " <> f)

evalDefine :: Presentation -> SurfaceDef -> MorphismEnv -> CoreEnv -> Define -> [CoreExpr] -> Either Text CoreVal
evalDefine pres surf morphs env def args = do
  args' <- mapM (evalCoreExpr pres surf morphs env) args
  tryClauses args' (defClauses def)
  where
    tryClauses vals [] =
      Left ("no matching define clause for " <> defName def <> " with args " <> T.pack (show vals))
    tryClauses vals (cl:cls) =
      case matchDefine surf env vals cl of
        Left _ -> tryClauses vals cls
        Right env' -> evalCoreExpr pres surf morphs env' (dcBody cl)

matchDefine :: SurfaceDef -> CoreEnv -> [CoreVal] -> DefineClause -> Either Text CoreEnv
matchDefine surf env vals clause =
  if length vals /= length (dcArgs clause)
    then Left "define arity mismatch"
    else do
      env1 <- foldM (matchArg surf) M.empty (zip (dcArgs clause) vals)
      env2 <- foldM (matchWhere surf) env1 (dcWhere clause)
      pure (M.union env2 env)

matchArg :: SurfaceDef -> CoreEnv -> (DefinePat, CoreVal) -> Either Text CoreEnv
matchArg surf env (pat, val) =
  case pat of
    DPVar name ->
      case M.lookup name env of
        Nothing -> Right (M.insert name val env)
        Just existing ->
          if existing == val then Right env else Left "define: conflicting variable"
    DPNat np ->
      case val of
        CVNat n -> bindNat env np n
        _ -> Left "define: expected nat"
    DPSurf p ->
      case val of
        CVSurf t ->
          case matchPTermRigid p t of
            Left err -> Left err
            Right Nothing -> Left "define: pattern mismatch"
            Right (Just sub) -> bindMatch env sub
        _ -> Left "define: expected surface term"
    DPCtx cp ->
      case val of
        CVCtx ctx -> bindCtxPat surf env cp ctx
        _ -> Left "define: expected context"

bindMatch :: CoreEnv -> MatchSubst -> Either Text CoreEnv
bindMatch env subst = do
  envTerms <- mapM toTerm (M.toList (msTerms subst))
  let envNats = M.fromList [ (k, CVNat v) | (k, v) <- M.toList (msNats subst) ]
  pure (M.union env (M.union (M.fromList envTerms) envNats))
  where
    toTerm (mv, ms) = do
      let args = map Ix [0 .. msArity ms - 1]
      tm <- instantiateMeta ms args
      pure (renderMVar mv, CVSurf tm)
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
lookupDefine name surf = M.lookup name (sdDefines surf)

resolveOpInterp :: MorphismEnv -> Text -> Either Text OpInterp
resolveOpInterp morphs name =
  case splitAlias name of
    Nothing -> Left "unqualified core name"
    Just (alias, slot) ->
      case M.lookup alias morphs of
        Nothing -> Left ("unknown core alias: " <> alias)
        Just mor ->
          case resolveOpNameIn (morSrc mor) slot of
            Left err -> Left err
            Right key ->
              lookupInterp mor key

splitAlias :: Text -> Maybe (Text, Text)
splitAlias name =
  let (a, rest) = T.breakOn "." name
  in if T.null rest
      then Nothing
      else Just (a, T.drop 1 rest)

resolveOpNameIn :: Presentation -> Text -> Either Text OpName
resolveOpNameIn pres name =
  let direct = OpName name
      pref = OpName (presName pres <> "." <> name)
      sig = presSig pres
  in if M.member direct (sigOps sig)
      then Right direct
      else if M.member pref (sigOps sig)
        then Right pref
        else Left ("unknown core op: " <> name)


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

checkOpArgs :: Text -> [Binder] -> [Term] -> Either Text ()
checkOpArgs name tele args = go M.empty tele args
  where
    go _ [] [] = Right ()
    go _ [] _ = Left ("core op arity mismatch: " <> name)
    go _ _ [] = Left ("core op arity mismatch: " <> name)
    go subst (Binder v s : bs) (a:as) =
      let expected = applySubstSort subst s
      in if termSort a == expected
          then go (M.insert v a subst) bs as
          else Left ("core op argument sort mismatch: " <> name)
