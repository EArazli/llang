{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.UnifyTy
  ( Subst(..)
  , emptySubst
  , unifyTy
  , unifyTyFlex
  , unifyIx
  , unifyCtx
  , applySubstTy
  , applySubstIx
  , applySubstCtx
  , normalizeSubst
  , composeSubst
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.IndexTheory
import Strat.Poly.ModeTheory (ModeName(..), ModName(..), ModExpr(..))
import Strat.Poly.TypeExpr
import Strat.Poly.TypeTheory


data Subst = Subst
  { sTy :: M.Map TyVar TypeExpr
  , sIx :: M.Map IxVar IxTerm
  } deriving (Eq, Ord, Show)

emptySubst :: Subst
emptySubst = Subst M.empty M.empty

unifyTy :: TypeTheory -> TypeExpr -> TypeExpr -> Either Text Subst
unifyTy tt t1 t2 =
  let tyFlex = S.union (freeTyVarsType t1) (freeTyVarsType t2)
      ixFlex = S.union (freeIxVarsType t1) (freeIxVarsType t2)
   in unifyTyFlex tt [] tyFlex ixFlex emptySubst t1 t2

unifyTyFlex
  :: TypeTheory
  -> [TypeExpr]
  -> S.Set TyVar
  -> S.Set IxVar
  -> Subst
  -> TypeExpr
  -> TypeExpr
  -> Either Text Subst
unifyTyFlex tt ixCtx tyFlex ixFlex subst t1 t2 = do
  t1' <- applySubstTy tt subst t1
  t2' <- applySubstTy tt subst t2
  unifyWith subst t1' t2'
  where
    unifyWith s a b =
      case (a, b) of
        (TVar v, t) -> unifyTyVar s v t
        (t, TVar v) -> unifyTyVar s v t
        (TCon refA argsA, TCon refB argsB)
          | refA == refB && length argsA == length argsB ->
              case M.lookup refA (ttTypeParams tt) of
                Just params
                  | length params == length argsA ->
                      foldl stepBySig (Right s) (zip params (zip argsA argsB))
                _ ->
                  foldl step (Right s) (zip argsA argsB)
          | otherwise ->
              Left ("unifyTyFlex: cannot unify " <> renderTy a <> " with " <> renderTy b)
        (TMod me1 x1, TMod me2 x2)
          | me1 == me2 -> unifyWith s x1 x2
          | otherwise -> Left ("unifyTyFlex: cannot unify " <> renderTy a <> " with " <> renderTy b)
        _ ->
          Left ("unifyTyFlex: cannot unify " <> renderTy a <> " with " <> renderTy b)

    step acc (argA, argB) = do
      s <- acc
      case (argA, argB) of
        (TAType tyA, TAType tyB) -> do
          tyA' <- applySubstTy tt s tyA
          tyB' <- applySubstTy tt s tyB
          s1 <- unifyTyFlex tt ixCtx tyFlex ixFlex s tyA' tyB'
          composeSubst tt s1 s
        (TAIndex ixA, TAIndex ixB) -> do
          sort <- inferExpectedIxSort tt ixCtx s ixA ixB
          s1 <- unifyIx tt ixCtx ixFlex s sort ixA ixB
          composeSubst tt s1 s
        _ -> Left "unifyTyFlex: mixed type/index arguments cannot unify"

    stepBySig acc (paramSig, (argA, argB)) = do
      s <- acc
      case (paramSig, argA, argB) of
        (TPS_Ty _, TAType tyA, TAType tyB) -> do
          tyA' <- applySubstTy tt s tyA
          tyB' <- applySubstTy tt s tyB
          s1 <- unifyTyFlex tt ixCtx tyFlex ixFlex s tyA' tyB'
          composeSubst tt s1 s
        (TPS_Ix sort, TAIndex ixA, TAIndex ixB) -> do
          s1 <- unifyIx tt ixCtx ixFlex s sort ixA ixB
          composeSubst tt s1 s
        (TPS_Ty _, _, _) ->
          Left "unifyTyFlex: expected type argument for constructor parameter"
        (TPS_Ix _, _, _) ->
          Left "unifyTyFlex: expected index argument for constructor parameter"

    unifyTyVar s v t
      | v `S.member` tyFlex = bindTyVar s v t
      | otherwise =
          case t of
            TVar v' | v == v' -> Right s
            TVar v' | v' `S.member` tyFlex -> bindTyVar s v' (TVar v)
            _ -> Left ("unifyTyFlex: rigid variable mismatch " <> renderVar v <> " with " <> renderTy t)

    bindTyVar s v t = do
      t' <- applySubstTy tt s t
      if tvMode v /= typeMode t'
        then Left ("unifyTyFlex: mode mismatch " <> renderVar v <> " with " <> renderTy t')
        else if t' == TVar v
          then Right s
          else if occursTyVar v t'
            then Left ("unifyTyFlex: occurs check failed for " <> renderVar v <> " in " <> renderTy t')
            else composeSubst tt (Subst (M.singleton v t') M.empty) s

unifyCtx
  :: TypeTheory
  -> [TypeExpr]
  -> S.Set TyVar
  -> S.Set IxVar
  -> Context
  -> Context
  -> Either Text Subst
unifyCtx tt ixCtx tyFlex ixFlex ctx1 ctx2
  | length ctx1 /= length ctx2 = Left "unifyCtx: length mismatch"
  | otherwise = foldl step (Right emptySubst) (zip ctx1 ctx2)
  where
    step acc (a, b) = do
      s <- acc
      a' <- applySubstTy tt s a
      b' <- applySubstTy tt s b
      s1 <- unifyTyFlex tt ixCtx tyFlex ixFlex s a' b'
      composeSubst tt s1 s

unifyIx
  :: TypeTheory
  -> [TypeExpr]
  -> S.Set IxVar
  -> Subst
  -> TypeExpr
  -> IxTerm
  -> IxTerm
  -> Either Text Subst
unifyIx tt ixCtx ixFlex subst expectedSort ix1 ix2 = do
  expectedSort0 <- applySubstTy tt subst expectedSort
  expectedSort' <- normalizeTypeDeep tt expectedSort0
  lhs0 <- applySubstIx tt subst expectedSort' ix1
  rhs0 <- applySubstIx tt subst expectedSort' ix2
  lhs <- normalizeIx tt expectedSort' lhs0
  rhs <- normalizeIx tt expectedSort' rhs0
  unifyIxNorm subst expectedSort' lhs rhs
  where
    unifyIxNorm s currentSort a b =
      case (a, b) of
        (IXBound i, IXBound j) -> do
          checkBoundSort s currentSort i
          checkBoundSort s currentSort j
          if i == j
            then Right s
            else Left "unifyIx: bound index mismatch"
        (IXFun f xs, IXFun g ys)
          | f == g && length xs == length ys -> do
              sig <- requireFunSig s currentSort f xs
              foldl step (Right s) (zip3 (ifArgs sig) xs ys)
          | otherwise -> Left "unifyIx: function mismatch"
        (IXVar v, IXVar w) -> do
          checkIxVarSort s currentSort v
          checkIxVarSort s currentSort w
          if sameIxVarId v w
            then Right s
            else
              if v `S.member` ixFlex
                then bindIxVar s currentSort v (IXVar w)
                else
                  if w `S.member` ixFlex
                    then bindIxVar s currentSort w (IXVar v)
                    else Left "unifyIx: rigid index variable mismatch"
        (IXVar v, t) -> do
          checkIxVarSort s currentSort v
          ensureIxTermSort s currentSort t
          if v `S.member` ixFlex
            then bindIxVar s currentSort v t
            else Left "unifyIx: rigid index variable mismatch"
        (t, IXVar v) -> do
          checkIxVarSort s currentSort v
          ensureIxTermSort s currentSort t
          if v `S.member` ixFlex
            then bindIxVar s currentSort v t
            else Left "unifyIx: rigid index variable mismatch"
        _ -> Left "unifyIx: cannot unify index terms"
      where
        step acc (argSort, x, y) = do
          s1 <- acc
          argSort0 <- applySubstTy tt s1 argSort
          argSort' <- normalizeTypeDeep tt argSort0
          x' <- applySubstIx tt s1 argSort' x
          y' <- applySubstIx tt s1 argSort' y
          xNorm <- normalizeIx tt argSort' x'
          yNorm <- normalizeIx tt argSort' y'
          s2 <- unifyIxNorm s1 argSort' xNorm yNorm
          composeSubst tt s2 s1

    bindIxVar s currentSort v t = do
      sortV0 <- applySubstTy tt s (ixvSort v)
      sortV <- normalizeTypeDeep tt sortV0
      currentSort' <- normalizeTypeDeep tt currentSort
      if sortV /= currentSort'
        then Left "unifyIx: variable sort mismatch"
        else Right ()
      t' <- applySubstIx tt s sortV t
      ensureIxTermSort s sortV t'
      if occursIxVar v t'
        then Left "unifyIx: occurs check failed"
        else do
          let boundSet = boundIxIndicesIx t'
          if any (>= ixvScope v) (S.toList boundSet)
            then Left "unifyIx: escape from index scope"
            else if ixvScope v == 0 && not (S.null boundSet)
              then Left "unifyIx: scope-0 metavariable cannot mention bound indices"
              else composeSubst tt (Subst M.empty (M.singleton v t')) s

    checkIxVarSort s currentSort v = do
      sortV0 <- applySubstTy tt s (ixvSort v)
      sortV <- normalizeTypeDeep tt sortV0
      currentSort' <- normalizeTypeDeep tt currentSort
      if sortV == currentSort'
        then Right ()
        else Left "unifyIx: index variable sort mismatch"

    checkBoundSort s currentSort i =
      if i < length ixCtx
        then do
          boundSort0 <- applySubstTy tt s (ixCtx !! i)
          boundSort <- normalizeTypeDeep tt boundSort0
          currentSort' <- normalizeTypeDeep tt currentSort
          if boundSort == currentSort'
            then Right ()
            else Left "unifyIx: bound index sort mismatch"
        else Left "unifyIx: bound index out of scope"

    ensureIxTermSort s currentSort tm =
      case tm of
        IXVar v -> checkIxVarSort s currentSort v
        IXBound i -> checkBoundSort s currentSort i
        IXFun f args -> do
          sig <- requireFunSig s currentSort f args
          mapM_ (uncurry (ensureIxTermSort s)) (zip (ifArgs sig) args)

    requireFunSig s currentSort f args = do
      currentSort0 <- applySubstTy tt s currentSort
      currentSort' <- normalizeTypeDeep tt currentSort0
      ixTheory <- requireTheoryForSort currentSort'
      sig <-
        case M.lookup f (itFuns ixTheory) of
          Nothing -> Left "unifyIx: unknown index function"
          Just sig' -> Right sig'
      if length (ifArgs sig) /= length args
        then Left "unifyIx: function arity mismatch"
        else Right ()
      resSort0 <- applySubstTy tt s (ifRes sig)
      resSort <- normalizeTypeDeep tt resSort0
      if resSort == currentSort'
        then Right sig
        else Left "unifyIx: function result sort mismatch"

    requireTheoryForSort sortTy =
      case M.lookup (typeMode sortTy) (ttIndex tt) of
        Nothing -> Left "unifyIx: expected sort is not in an index mode"
        Just ixTheory -> Right ixTheory

applySubstTy :: TypeTheory -> Subst -> TypeExpr -> Either Text TypeExpr
applySubstTy tt subst ty = do
  raw <- goTy S.empty ty
  normalizeTypeDeep tt raw
  where
    goTy seen expr =
      case expr of
        TVar v ->
          case M.lookup v (sTy subst) of
            Nothing -> Right (TVar v)
            Just t ->
              if v `S.member` seen
                then Right (TVar v)
                else goTy (S.insert v seen) t
        TCon ref args -> do
          args' <-
            case M.lookup ref (ttTypeParams tt) of
              Just params ->
                if length params /= length args
                  then Left "applySubstTy: type constructor arity mismatch"
                  else mapM (goArgBySig seen) (zip params args)
              Nothing ->
                mapM (goArgNoSig seen) args
          Right (TCon ref args')
        TMod me inner -> TMod me <$> goTy seen inner

    goArgBySig seen (param, arg) =
      case (param, arg) of
        (TPS_Ty _, TAType innerTy) ->
          TAType <$> goTy seen innerTy
        (TPS_Ix sortTy, TAIndex ix) -> do
          sort' <- goTy seen sortTy
          TAIndex <$> applySubstIx tt subst sort' ix
        (TPS_Ty _, TAIndex _) ->
          Left "applySubstTy: expected type argument for constructor parameter"
        (TPS_Ix _, TAType _) ->
          Left "applySubstTy: expected index argument for constructor parameter"

    goArgNoSig seen arg =
      case arg of
        TAType innerTy -> TAType <$> goTy seen innerTy
        TAIndex ix -> TAIndex <$> applyIxNoNorm seen ix

    applyIxNoNorm seen tm =
      case tm of
        IXVar v -> do
          sort' <- goTy seen (ixvSort v)
          case lookupIxById v (sIx subst) of
            Nothing -> Right (IXVar v { ixvSort = sort' })
            Just tmSub -> applyIxNoNorm seen tmSub
        IXBound _ -> Right tm
        IXFun f args -> IXFun f <$> mapM (applyIxNoNorm seen) args

applySubstIx :: TypeTheory -> Subst -> TypeExpr -> IxTerm -> Either Text IxTerm
applySubstIx tt subst expectedSort tm = do
  expectedSort' <- applySubstTy tt subst expectedSort
  tm' <- goIx S.empty tm
  normalizeIx tt expectedSort' tm'
  where
    goIx seen expr =
      case expr of
        IXVar v -> do
          sort' <- applySubstTy tt subst (ixvSort v)
          let v' = v { ixvSort = sort' }
          case lookupIxById v' (sIx subst) of
            Nothing -> Right (IXVar v')
            Just tmSub ->
              if v' `S.member` seen
                then Right (IXVar v')
                else goIx (S.insert v' seen) tmSub
        IXBound _ -> Right expr
        IXFun name args -> IXFun name <$> mapM (goIx seen) args

applySubstCtx :: TypeTheory -> Subst -> Context -> Either Text Context
applySubstCtx tt subst = mapM (applySubstTy tt subst)

normalizeSubst :: TypeTheory -> Subst -> Either Text Subst
normalizeSubst tt subst = do
  tyPairs <- mapM normTy (M.toList (sTy subst))
  ixPairs <- mapM normIx (M.toList (sIx subst))
  let tyMap = M.fromList [ (v, t) | (v, t) <- tyPairs, t /= TVar v ]
  let ixMap = M.fromList [ (v, t) | (v, t) <- ixPairs, t /= IXVar v ]
  Right (Subst tyMap ixMap)
  where
    normTy (v, t) = do
      t' <- applySubstTy tt subst t
      pure (v, t')
    normIx (v, t) = do
      sort' <- applySubstTy tt subst (ixvSort v)
      t' <- applySubstIx tt subst sort' t
      pure (v { ixvSort = sort' }, t')

composeSubst :: TypeTheory -> Subst -> Subst -> Either Text Subst
composeSubst tt s2 s1 = do
  ty1' <- mapM (applySubstTy tt s2) (sTy s1)
  ix1' <- fmap M.fromList (mapM substIxPair (M.toList (sIx s1)))
  normalizeSubst tt (Subst (M.union ty1' (sTy s2)) (M.union ix1' (sIx s2)))
  where
    substIxPair (v, t) = do
      sort' <- applySubstTy tt s2 (ixvSort v)
      t' <- applySubstIx tt s2 sort' t
      pure (v { ixvSort = sort' }, t')

inferExpectedIxSort :: TypeTheory -> [TypeExpr] -> Subst -> IxTerm -> IxTerm -> Either Text TypeExpr
inferExpectedIxSort tt ixCtx subst lhs rhs =
  case inferIxSortFromTerm tt ixCtx subst lhs of
    Right ty -> Right ty
    Left _ -> inferIxSortFromTerm tt ixCtx subst rhs

inferIxSortFromTerm :: TypeTheory -> [TypeExpr] -> Subst -> IxTerm -> Either Text TypeExpr
inferIxSortFromTerm tt ixCtx subst tm =
  case tm of
    IXVar v -> applySubstTy tt subst (ixvSort v)
    IXBound i ->
      if i < length ixCtx
        then applySubstTy tt subst (ixCtx !! i)
        else Left "inferIxSortFromTerm: out-of-scope bound index"
    IXFun f args -> do
      sig <- chooseFunSig f (length args)
      applySubstTy tt subst (ifRes sig)
  where
    chooseFunSig funName arity =
      case [ sig
           | ixTheory <- M.elems (ttIndex tt)
           , (name, sig) <- M.toList (itFuns ixTheory)
           , name == funName
           , length (ifArgs sig) == arity
           ] of
        [] -> Left "inferIxSortFromTerm: unknown index function"
        (sig:_) -> Right sig

occursTyVar :: TyVar -> TypeExpr -> Bool
occursTyVar v ty =
  case ty of
    TVar v' -> v == v'
    TCon _ args -> any occursArg args
    TMod _ inner -> occursTyVar v inner
  where
    occursArg arg =
      case arg of
        TAType innerTy -> occursTyVar v innerTy
        TAIndex ix -> any (occursTyVar v . ixvSort) (S.toList (freeIxVarsIx ix))

occursIxVar :: IxVar -> IxTerm -> Bool
occursIxVar v tm =
  case tm of
    IXVar v' -> sameIxVarId v v'
    IXBound _ -> False
    IXFun _ args -> any (occursIxVar v) args

sameIxVarId :: IxVar -> IxVar -> Bool
sameIxVarId a b = ixvName a == ixvName b && ixvScope a == ixvScope b

lookupIxById :: IxVar -> M.Map IxVar IxTerm -> Maybe IxTerm
lookupIxById v mp =
  case M.lookup v mp of
    Just tm -> Just tm
    Nothing ->
      snd <$> findIxById (M.toList mp)
  where
    findIxById [] = Nothing
    findIxById ((k, tm):rest)
      | sameIxVarId k v = Just (k, tm)
      | otherwise = findIxById rest

freeTyVarsType :: TypeExpr -> S.Set TyVar
freeTyVarsType ty =
  case ty of
    TVar v -> S.singleton v
    TCon _ args -> S.unions (map freeArg args)
    TMod _ inner -> freeTyVarsType inner
  where
    freeArg arg =
      case arg of
        TAType innerTy -> freeTyVarsType innerTy
        TAIndex ix -> S.unions (map (freeTyVarsType . ixvSort) (S.toList (freeIxVarsIx ix)))

renderTy :: TypeExpr -> Text
renderTy ty =
  case ty of
    TVar v -> renderVar v
    TCon ref [] -> renderTypeRef ref
    TCon ref args ->
      renderTypeRef ref <> "(" <> T.intercalate ", " (map renderArg args) <> ")"
    TMod me inner -> renderModExpr me <> "(" <> renderTy inner <> ")"
  where
    renderArg arg =
      case arg of
        TAType innerTy -> renderTy innerTy
        TAIndex ix -> renderIx ix

    renderIx tm =
      case tm of
        IXVar v -> ixvName v
        IXBound i -> "^" <> T.pack (show i)
        IXFun f [] -> renderIxFun f
        IXFun f args -> renderIxFun f <> "(" <> T.intercalate ", " (map renderIx args) <> ")"

    renderIxFun (IxFunName n) = n

renderVar :: TyVar -> Text
renderVar v = tvName v <> "@" <> renderMode (tvMode v)

renderTypeRef :: TypeRef -> Text
renderTypeRef ref =
  renderMode (trMode ref) <> "." <> renderTypeName (trName ref)

renderTypeName :: TypeName -> Text
renderTypeName (TypeName n) = n

renderMode :: ModeName -> Text
renderMode (ModeName n) = n

renderModExpr :: ModExpr -> Text
renderModExpr me =
  case reverse (mePath me) of
    [] -> "id@" <> renderMode (meSrc me)
    names -> T.intercalate "." (map renderModName names)

renderModName :: ModName -> Text
renderModName (ModName n) = n
