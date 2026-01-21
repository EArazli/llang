{-# LANGUAGE OverloadedStrings #-}
module Strat.Surface2.Engine
  ( Ctx(..)
  , emptyCtx
  , extendCtx
  , lookupCtx
  , GoalArg(..)
  , SolveEnv(..)
  , SolveResult(..)
  , SolveError(..)
  , renderSolveError
  , solveJudgment
  ) where

import Strat.Surface2.Def
import Strat.Surface2.Pattern
import Strat.Surface2.Term
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Control.Monad (foldM)
import Data.List (foldl')

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

data SolveError
  = AmbiguousRules { seGoal :: JudgName, seCandidates :: [Text] }
  | NoRuleApplies { seGoal :: JudgName, seAttempted :: [(Text, Text)] }
  | SolverFuelExhausted
  deriving (Eq, Show)

renderSolveError :: SolveError -> Text
renderSolveError err =
  case err of
    AmbiguousRules goal names ->
      "surface solver: ambiguous rules for " <> renderJudg goal <> " (" <> T.intercalate ", " names <> ")"
    NoRuleApplies goal attempts ->
      let detail = T.intercalate "; " [ n <> ": " <> msg | (n, msg) <- attempts ]
      in "surface solver: no rule applies to " <> renderJudg goal <> if T.null detail then "" else " (" <> detail <> ")"
    SolverFuelExhausted -> "surface solver: fuel exhausted"

renderJudg :: JudgName -> Text
renderJudg (JudgName t) = t

solveJudgment :: SurfaceDef -> JudgName -> [GoalArg] -> Int -> Either SolveError SolveResult
solveJudgment surf judg args fuel =
  fmap fst (solveGoal surf fuel judg args 0)

solveGoal :: SurfaceDef -> Int -> JudgName -> [GoalArg] -> Int -> Either SolveError (SolveResult, Int)
solveGoal surf fuel judg args supply
  | fuel <= 0 = Left SolverFuelExhausted
  | otherwise =
      let candidates = [ r | r <- sdRules surf, rcJudg (rdConclusion r) == judg ]
          attempts = [ (r, attemptRule supply r) | r <- candidates ]
          successes = [ (rdName r, res) | (r, Right res) <- attempts ]
          failures = [ (rdName r, err) | (r, Left err) <- attempts ]
      in case successes of
          [] -> Left (NoRuleApplies judg failures)
          [( _, res)] -> Right res
          xs -> Left (AmbiguousRules judg (map fst xs))
  where
    attemptRule s r =
      let (r', s') = freshenRule s r
      in case applyRule r' s' of
          Left err -> Left err
          Right res -> Right res

    applyRule rule s = do
      env0 <- matchConclusion (rdConclusion rule) args
      (env1, s') <- solvePremises surf (fuel - 1) env0 (rdPremises rule) s
      let outs = rcOutputs (rdConclusion rule)
      pure (SolveResult { srOutputs = outs, srEnv = env1 }, s')

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
  case matchPTermWithSubst True (seMatch env) pat term of
    Left err -> Left err
    Right Nothing -> Left "surface solver: pattern mismatch"
    Right (Just sub) -> Right (seedAfterMatch env sub)
  where
    seedAfterMatch env' sub =
      let seeded = seedMetas sub pat
      in env' { seMatch = seeded }

seedMetas :: MatchSubst -> PTerm -> MatchSubst
seedMetas subst pat =
  foldl' seedMeta subst (collectMeta0 pat)
  where
    metaPlaceholder name = "_" <> name
    seedMeta s mv@(MVar name) =
      if M.member mv (msTerms s)
        then s
        else s { msTerms = M.insert mv (MetaSubst 0 (SFree (metaPlaceholder name))) (msTerms s) }

collectMeta0 :: PTerm -> [MVar]
collectMeta0 pat =
  case pat of
    PMeta mv [] -> [mv]
    PMeta _ _ -> []
    PCon _ args -> concatMap collectArg args
    PBound _ -> []
    PBoundVar _ -> []
    PFree _ -> []

collectArg :: PArg -> [MVar]
collectArg (PArg binders body) =
  concatMap collectMeta0 binders <> collectMeta0 body

mergeMatchSubst :: MatchSubst -> MatchSubst -> Either Text MatchSubst
mergeMatchSubst a b = do
  terms <- mergeTerms (msTerms a) (msTerms b)
  nats <- mergeNats (msNats a) (msNats b)
  pure MatchSubst { msTerms = terms, msNats = nats }
  where
    mergeNats left right =
      let dup = M.keys (M.intersection left right)
      in case dup of
          [] -> Right (M.union left right)
          (k:_) ->
            if left M.! k == right M.! k
              then Right (M.union left right)
              else Left "surface solver: conflicting nat variable binding"

    mergeTerms left right = foldM step left (M.toList right)
      where
        step acc (k, v) =
          case M.lookup k acc of
            Nothing -> Right (M.insert k v acc)
            Just v' ->
              case resolveConflict k v' v of
                Just v'' -> Right (M.insert k v'' acc)
                Nothing -> Left "surface solver: conflicting metavariable binding"

        resolveConflict mv v1 v2
          | v1 == v2 = Just v1
          | isSelfPlaceholder mv v1 = Just v2
          | isSelfPlaceholder mv v2 = Just v1
          | otherwise = Nothing

    isSelfPlaceholder (MVar name) ms =
      msArity ms == 0 && msBody ms == SFree ("_" <> name)

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

solvePremises :: SurfaceDef -> Int -> SolveEnv -> [RulePremise] -> Int -> Either Text (SolveEnv, Int)
solvePremises _ _ env [] supply = Right (env, supply)
solvePremises surf fuel env (p:ps) supply = do
  (env', supply') <- solvePremise surf fuel env p supply
  solvePremises surf fuel env' ps supply'

solvePremise :: SurfaceDef -> Int -> SolveEnv -> RulePremise -> Int -> Either Text (SolveEnv, Int)
solvePremise surf fuel env prem supply =
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
      pure (env { seMatch = match' }, supply)
    PremiseJudg judg args outs under -> do
      args' <- mapM (instantiateArg env) args
      ctx' <- applyUnder surf env under
      let args'' = replaceCtx args' ctx'
      (res, supply') <-
        case solveGoal surf (fuel - 1) judg args'' supply of
          Left err -> Left (renderSolveError err)
          Right ok -> Right ok
      let avoid = S.fromList outs `S.union` M.keysSet (seCore env)
      let (subCore', outputs') = freshenCore avoid (seCore (srEnv res)) (srOutputs res)
      let coreBindings = M.fromList (zip outs outputs')
      let coreFromPremise = M.union coreBindings subCore'
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
      pure
        ( env
            { seCore = mergedCore
            , seMatch = mergedMatch
            , seCtxs = mergedCtx
            , seSurfVars = mergedSurf
            }
        , supply'
        )

freshenRule :: Int -> RuleDef -> (RuleDef, Int)
freshenRule n rule =
  let suffix = "_" <> T.pack (show n)
      renameName name =
        case M.lookup name mapping of
          Just name' -> name'
          Nothing -> name
      mapping = M.fromList [ (name, name <> suffix) | name <- S.toList names ]
      names = collectRuleNames rule
      rule' =
        rule
          { rdConclusion = renameConclusion renameName (rdConclusion rule)
          , rdPremises = map (renamePremise renameName) (rdPremises rule)
          }
  in (rule', n + 1)

collectRuleNames :: RuleDef -> S.Set Text
collectRuleNames rule =
  S.unions
    [ collectConclusion (rdConclusion rule)
    , S.unions (map collectPremise (rdPremises rule))
    ]

collectConclusion :: RuleConclusion -> S.Set Text
collectConclusion concl =
  S.unions (map collectArgPat (rcArgs concl))

collectPremise :: RulePremise -> S.Set Text
collectPremise prem =
  case prem of
    PremiseLookup ctxName idxPat outName ->
      S.unions [S.singleton ctxName, S.singleton outName, collectNatPat idxPat]
    PremiseJudg _ args outs under ->
      S.unions
        [ S.unions (map collectArgPat args)
        , S.fromList outs
        , collectUnder under
        ]

collectUnder :: Maybe UnderCtx -> S.Set Text
collectUnder Nothing = S.empty
collectUnder (Just under) =
  S.insert (ucCtx under) (collectPTerm (ucType under))

collectArgPat :: ArgPat -> S.Set Text
collectArgPat pat =
  case pat of
    ArgSurf p -> collectPTerm p
    ArgCtx name -> S.singleton name
    ArgNat np -> collectNatPat np

collectNatPat :: NatPat -> S.Set Text
collectNatPat np =
  case np of
    NatZero -> S.empty
    NatSucc name -> S.singleton name
    NatVar name -> S.singleton name

collectPTerm :: PTerm -> S.Set Text
collectPTerm pat =
  case pat of
    PBound _ -> S.empty
    PBoundVar name -> S.singleton name
    PFree _ -> S.empty
    PMeta (MVar name) _ -> S.singleton name
    PCon _ args -> S.unions (map collectPArg args)

collectPArg :: PArg -> S.Set Text
collectPArg (PArg binders body) =
  S.unions (map collectPTerm binders) `S.union` collectPTerm body

renameConclusion :: (Text -> Text) -> RuleConclusion -> RuleConclusion
renameConclusion f concl =
  concl
    { rcArgs = map (renameArgPat f) (rcArgs concl)
    , rcOutputs = map (renameCoreExpr f) (rcOutputs concl)
    }

renamePremise :: (Text -> Text) -> RulePremise -> RulePremise
renamePremise f prem =
  case prem of
    PremiseLookup ctxName idxPat outName ->
      PremiseLookup (f ctxName) (renameNatPat f idxPat) (f outName)
    PremiseJudg judg args outs under ->
      PremiseJudg judg
        (map (renameArgPat f) args)
        (map f outs)
        (renameUnder f under)

renameUnder :: (Text -> Text) -> Maybe UnderCtx -> Maybe UnderCtx
renameUnder _ Nothing = Nothing
renameUnder f (Just under) =
  Just under
    { ucCtx = f (ucCtx under)
    , ucType = renamePTerm f (ucType under)
    }

renameArgPat :: (Text -> Text) -> ArgPat -> ArgPat
renameArgPat f pat =
  case pat of
    ArgSurf p -> ArgSurf (renamePTerm f p)
    ArgCtx name -> ArgCtx (f name)
    ArgNat np -> ArgNat (renameNatPat f np)

renameNatPat :: (Text -> Text) -> NatPat -> NatPat
renameNatPat f np =
  case np of
    NatZero -> NatZero
    NatSucc name -> NatSucc (f name)
    NatVar name -> NatVar (f name)

renamePTerm :: (Text -> Text) -> PTerm -> PTerm
renamePTerm f pat =
  case pat of
    PBound ix -> PBound ix
    PBoundVar name -> PBoundVar (f name)
    PFree name -> PFree name
    PMeta (MVar name) ixs -> PMeta (MVar (f name)) ixs
    PCon con args -> PCon con (map (renamePArg f) args)

renamePArg :: (Text -> Text) -> PArg -> PArg
renamePArg f (PArg binders body) =
  PArg (map (renamePTerm f) binders) (renamePTerm f body)

renameCoreExpr :: (Text -> Text) -> CoreExpr -> CoreExpr
renameCoreExpr f expr =
  case expr of
    CoreVar name -> CoreVar (f name)
    CoreApp fun args -> CoreApp fun (map (renameCoreExpr f) args)

freshenCore :: S.Set Text -> M.Map Text CoreExpr -> [CoreExpr] -> (M.Map Text CoreExpr, [CoreExpr])
freshenCore avoid subCore outputs =
  let (renameMap, _) = foldl' step (M.empty, avoid) (M.keys subCore)
      renameKey name = M.findWithDefault name name renameMap
      renameExpr = renameCoreVars renameMap
      subCore' = M.fromList
        [ (renameKey k, renameExpr v)
        | (k, v) <- M.toList subCore
        ]
      outputs' = map renameExpr outputs
  in (subCore', outputs')
  where
    step (m, used) name =
      if name `S.member` used
        then
          let name' = freshName name used
          in (M.insert name name' m, S.insert name' used)
        else (m, S.insert name used)
    freshName base used = go (0 :: Int)
      where
        go n =
          let suffix = if n == 0 then "_sub" else "_sub" <> T.pack (show n)
              candidate = base <> suffix
          in if candidate `S.member` used then go (n + 1) else candidate

renameCoreVars :: M.Map Text Text -> CoreExpr -> CoreExpr
renameCoreVars mapping expr =
  case expr of
    CoreVar name -> CoreVar (M.findWithDefault name name mapping)
    CoreApp f args -> CoreApp f (map (renameCoreVars mapping) args)

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
    ArgSurf p -> GSurf <$> applySubstPTerm (seMatch env) p
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

applyUnder :: SurfaceDef -> SolveEnv -> Maybe UnderCtx -> Either Text (Maybe Ctx)
applyUnder _ _ Nothing = Right Nothing
applyUnder _ env (Just under) =
  case M.lookup (ucCtx under) (seCtxs env) of
    Nothing -> Right Nothing
    Just ctx -> do
      ty <- applySubstPTerm (seMatch env) (ucType under)
      Right (Just (extendCtx ctx ty))

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
