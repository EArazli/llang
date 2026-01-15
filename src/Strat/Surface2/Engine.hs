{-# LANGUAGE OverloadedStrings #-}
module Strat.Surface2.Engine
  ( Ctx(..)
  , emptyCtx
  , extendCtx
  , lookupCtx
  , GoalArg(..)
  , SolveEnv(..)
  , SolveResult(..)
  , solveJudgment
  ) where

import Strat.Surface2.Def
import Strat.Surface2.Pattern
import Strat.Surface2.Term
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import Control.Monad (foldM)

data Ctx = Ctx [STerm]
  deriving (Eq, Show)

emptyCtx :: Ctx
emptyCtx = Ctx []

extendCtx :: Ctx -> STerm -> Ctx
extendCtx (Ctx xs) ty = Ctx (xs <> [ty])

lookupCtx :: Ctx -> Int -> Maybe STerm
lookupCtx (Ctx xs) i =
  let idx = length xs - 1 - i
  in if idx >= 0 && idx < length xs then Just (xs !! idx) else Nothing

data GoalArg
  = GSurf STerm
  | GCtx Ctx
  | GNat Int
  deriving (Eq, Show)

data SolveEnv = SolveEnv
  { seMatch :: MatchSubst
  , seCtxs :: M.Map Text Ctx
  , seCore :: M.Map Text CoreExpr
  , seSurfVars :: M.Map Text STerm
  } deriving (Eq, Show)

data SolveResult = SolveResult
  { srOutputs :: [CoreExpr]
  , srEnv :: SolveEnv
  } deriving (Eq, Show)

solveJudgment :: SurfaceDef -> JudgName -> [GoalArg] -> Int -> Either Text SolveResult
solveJudgment surf judg args fuel =
  solveGoal surf fuel judg args

solveGoal :: SurfaceDef -> Int -> JudgName -> [GoalArg] -> Either Text SolveResult
solveGoal surf fuel judg args
  | fuel <= 0 = Left "surface solver: fuel exhausted"
  | otherwise = tryRules (sdRules surf)
  where
    tryRules [] = Left "surface solver: no rule applies"
    tryRules (r:rs)
      | rcJudg (rdConclusion r) /= judg = tryRules rs
      | otherwise =
          case applyRule r of
            Left _ -> tryRules rs
            Right res -> Right res

    applyRule rule = do
      env0 <- matchConclusion (rdConclusion rule) args
      env1 <- solvePremises surf (fuel - 1) env0 (rdPremises rule)
      let outs = rcOutputs (rdConclusion rule)
      pure SolveResult { srOutputs = outs, srEnv = env1 }

matchConclusion :: RuleConclusion -> [GoalArg] -> Either Text SolveEnv
matchConclusion concl args =
  if length (rcArgs concl) /= length args
    then Left "surface solver: goal arity mismatch"
    else do
      let env0 = SolveEnv (MatchSubst M.empty M.empty) M.empty M.empty M.empty
      foldM matchArg env0 (zip (rcArgs concl) args)

matchArg :: SolveEnv -> (ArgPat, GoalArg) -> Either Text SolveEnv
matchArg env (pat, arg) =
  case (pat, arg) of
    (ArgSurf p, GSurf t) -> matchSurf env p t
    (ArgCtx name, GCtx ctx) -> bindCtx env name ctx
    (ArgNat np, GNat n) -> bindNat env np n
    _ -> Left "surface solver: argument mismatch"

matchSurf :: SolveEnv -> PTerm -> STerm -> Either Text SolveEnv
matchSurf env pat term =
  case term of
    SFree name | isPlaceholder name ->
      case matchPTerm pat term of
        Nothing -> Left "surface solver: pattern mismatch"
        Just sub -> mergeMatch env sub
    SFree name ->
      case M.lookup name (seSurfVars env) of
        Nothing -> do
          let tm = applySubstPTerm (seMatch env) pat
          pure env { seSurfVars = M.insert name tm (seSurfVars env) }
        Just tm ->
          if tm == applySubstPTerm (seMatch env) pat
            then Right env
            else Left "surface solver: conflicting surface placeholder"
    _ ->
      case matchPTerm pat term of
        Nothing -> Left "surface solver: pattern mismatch"
        Just sub -> mergeMatch env sub
  where
    isPlaceholder name = T.isPrefixOf (T.singleton '_') name

mergeMatch :: SolveEnv -> MatchSubst -> Either Text SolveEnv
mergeMatch env sub = do
  merged <- mergeMatchSubst (seMatch env) sub
  pure env { seMatch = merged }

mergeMatchSubst :: MatchSubst -> MatchSubst -> Either Text MatchSubst
mergeMatchSubst a b = do
  terms <- mergeMap msTerms "metavariable" a b
  nats <- mergeMap msNats "nat variable" a b
  pure MatchSubst { msTerms = terms, msNats = nats }
  where
    mergeMap sel label x y =
      let left = sel x
          right = sel y
          dup = M.keys (M.intersection left right)
      in case dup of
          [] -> Right (M.union left right)
          (k:_) ->
            if left M.! k == right M.! k
              then Right (M.union left right)
              else Left ("surface solver: conflicting " <> label <> " binding")

bindCtx :: SolveEnv -> Text -> Ctx -> Either Text SolveEnv
bindCtx env name ctx =
  case M.lookup name (seCtxs env) of
    Nothing -> Right env { seCtxs = M.insert name ctx (seCtxs env) }
    Just ctx' -> if ctx' == ctx then Right env else Left "surface solver: conflicting context binding"

bindNat :: SolveEnv -> NatPat -> Int -> Either Text SolveEnv
bindNat env np n =
  case np of
    NatZero -> if n == 0 then Right env else Left "surface solver: nat mismatch"
    NatSucc name ->
      if n > 0
        then bindNatVar env name (n - 1)
        else Left "surface solver: nat mismatch"
    NatVar name -> bindNatVar env name n

bindNatVar :: SolveEnv -> Text -> Int -> Either Text SolveEnv
bindNatVar env name n =
  case M.lookup name (msNats (seMatch env)) of
    Nothing ->
      let match' = (seMatch env) { msNats = M.insert name n (msNats (seMatch env)) }
      in Right env { seMatch = match' }
    Just n' -> if n' == n then Right env else Left "surface solver: conflicting nat binding"

solvePremises :: SurfaceDef -> Int -> SolveEnv -> [RulePremise] -> Either Text SolveEnv
solvePremises _ _ env [] = Right env
solvePremises surf fuel env (p:ps) = do
  env' <- solvePremise surf fuel env p
  solvePremises surf fuel env' ps

solvePremise :: SurfaceDef -> Int -> SolveEnv -> RulePremise -> Either Text SolveEnv
solvePremise surf fuel env prem =
  case prem of
    PremiseLookup ctxName idxPat outName -> do
      ctx <- requireCtx env ctxName
      idx <- evalNatPat (seMatch env) idxPat
      ty <- case lookupCtx ctx idx of
        Nothing -> Left "surface solver: lookup out of bounds"
        Just t -> Right t
      let m = MVar outName
      let meta = MetaSubst 0 ty
      let match' = (seMatch env) { msTerms = M.insert m meta (msTerms (seMatch env)) }
      pure env { seMatch = match' }
    PremiseJudg judg args outs under -> do
      args' <- mapM (instantiateArg env) args
      let ctx' = applyUnder env under
      let args'' = replaceCtx args' ctx'
      res <- solveGoal surf (fuel - 1) judg args''
      let coreBindings = M.fromList (zip outs (srOutputs res))
      let coreFromPremise = M.union coreBindings (seCore (srEnv res))
      mergedMatch <- mergeMatchSubst (seMatch env) (seMatch (srEnv res))
      let (coreFromPremise', subCtxs) =
            case under of
              Nothing -> (coreFromPremise, seCtxs (srEnv res))
              Just u ->
                case ctx' of
                  Nothing -> (coreFromPremise, seCtxs (srEnv res))
                  Just underCtx ->
                    let fresh = freshCtxName (M.union (seCtxs env) (seCtxs (srEnv res))) (ucCtx u)
                        coreRenamed = M.map (renameCoreVar (ucCtx u) fresh) coreFromPremise
                        subCtxs' = M.insert fresh underCtx (M.delete (ucCtx u) (seCtxs (srEnv res)))
                    in (coreRenamed, subCtxs')
      mergedCtx <- mergeEqual "context" (seCtxs env) subCtxs
      mergedSurf <- mergeEqual "surface variable" (seSurfVars env) (seSurfVars (srEnv res))
      mergedCore <- mergeEqual "core binding" (seCore env) coreFromPremise'
      pure env
        { seCore = mergedCore
        , seMatch = mergedMatch
        , seCtxs = mergedCtx
        , seSurfVars = mergedSurf
        }

mergeEqual :: (Eq v) => Text -> M.Map Text v -> M.Map Text v -> Either Text (M.Map Text v)
mergeEqual label left right =
  case M.keys (M.intersection left right) of
    [] -> Right (M.union left right)
    (k:_) ->
      if left M.! k == right M.! k
        then Right (M.union left right)
        else Left ("surface solver: conflicting " <> label <> " binding")

instantiateArg :: SolveEnv -> ArgPat -> Either Text GoalArg
instantiateArg env pat =
  case pat of
    ArgSurf p -> Right (GSurf (applySubstPTerm (seMatch env) p))
    ArgCtx name -> requireCtx env name >>= \ctx -> Right (GCtx ctx)
    ArgNat np -> evalNatPat (seMatch env) np >>= \n -> Right (GNat n)

requireCtx :: SolveEnv -> Text -> Either Text Ctx
requireCtx env name =
  case M.lookup name (seCtxs env) of
    Nothing -> Left ("surface solver: unknown context " <> name)
    Just ctx -> Right ctx

evalNatPat :: MatchSubst -> NatPat -> Either Text Int
evalNatPat subst np =
  case np of
    NatZero -> Right 0
    NatSucc name -> do
      n <- lookupNat name
      Right (n + 1)
    NatVar name -> lookupNat name
  where
    lookupNat name =
      case M.lookup name (msNats subst) of
        Nothing -> Left ("surface solver: unbound nat variable " <> name)
        Just n -> Right n

applyUnder :: SolveEnv -> Maybe UnderCtx -> Maybe Ctx
applyUnder _ Nothing = Nothing
applyUnder env (Just under) =
  case M.lookup (ucCtx under) (seCtxs env) of
    Nothing -> Nothing
    Just ctx ->
      let ty = applySubstPTerm (seMatch env) (ucType under)
      in Just (extendCtx ctx ty)

replaceCtx :: [GoalArg] -> Maybe Ctx -> [GoalArg]
replaceCtx args Nothing = args
replaceCtx args (Just ctx) = map replace args
  where
    replace (GCtx _) = GCtx ctx
    replace other = other

freshCtxName :: M.Map Text Ctx -> Text -> Text
freshCtxName existing base = go (0 :: Int)
  where
    go n =
      let suffix = if n == 0 then "_under" else "_under" <> T.pack (show n)
          candidate = base <> suffix
      in if M.member candidate existing then go (n + 1) else candidate

renameCoreVar :: Text -> Text -> CoreExpr -> CoreExpr
renameCoreVar from to expr =
  case expr of
    CoreVar name -> CoreVar (if name == from then to else name)
    CoreApp f args -> CoreApp f (map (renameCoreVar from to) args)
