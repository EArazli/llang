{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.UnifyTy
  ( Subst(..)
  , emptySubst
  , unifyTy
  , unifyTyFlex
  , unifyTm
  , unifyCtx
  , applySubstTy
  , applySubstTm
  , applySubstCtx
  , normalizeSubst
  , composeSubst
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.IntMap.Strict as IM
import Control.Monad (foldM)
import Strat.Poly.ModeTheory (ModeName(..), ModName(..), ModExpr(..))
import Strat.Poly.Names (GenName(..))
import Strat.Poly.TypeExpr
import Strat.Poly.Graph
  ( Diagram(..)
  , Edge(..)
  , EdgePayload(..)
  , PortId(..)
  , diagramPortType
  , getPortLabel
  , unPortId
  , unEdgeId
  )
import qualified Strat.Poly.Diagram as Diag
import Strat.Poly.TypeTheory
  ( TypeTheory(..)
  , TypeParamSig(..)
  , TmFunSig(..)
  , lookupTmFunSig
  )
import Strat.Poly.TypeNormalize
  ( normalizeTypeDeep
  , normalizeTypeDeepWithCtx
  , normalizeTermDiagram
  , termToDiagram
  )
import Strat.Poly.TermExpr
  ( TermExpr(..)
  , diagramToTermExpr
  , termExprToDiagram
  , boundGlobalsExpr
  )


data Subst = Subst
  { sTy :: M.Map TyVar TypeExpr
  , sTm :: M.Map TmVar TermDiagram
  } deriving (Eq, Ord, Show)

data PortHead
  = PHBound Int
  | PHFun TmFunName [PortId]
  | PHMeta TmVar

emptySubst :: Subst
emptySubst = Subst M.empty M.empty

unifyTy :: TypeTheory -> TypeExpr -> TypeExpr -> Either Text Subst
unifyTy tt t1 t2 =
  let tyFlex = S.union (freeTyVarsType t1) (freeTyVarsType t2)
      tmFlex = S.union (freeTmVarsType t1) (freeTmVarsType t2)
   in unifyTyFlex tt [] tyFlex tmFlex emptySubst t1 t2

unifyTyFlex
  :: TypeTheory
  -> [TypeExpr]
  -> S.Set TyVar
  -> S.Set TmVar
  -> Subst
  -> TypeExpr
  -> TypeExpr
  -> Either Text Subst
unifyTyFlex tt tmCtx tyFlex tmFlex subst t1 t2 = do
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
        (TAType tyA, TAType tyB) ->
          unifyTyFlex tt tmCtx tyFlex tmFlex s tyA tyB
        (TATm tmA, TATm tmB) -> do
          sort <- inferExpectedTmSort tt tmCtx s tmA tmB
          unifyTm tt tmCtx tmFlex s sort tmA tmB
        _ -> Left "unifyTyFlex: mixed type/term arguments cannot unify"

    stepBySig acc (paramSig, (argA, argB)) = do
      s <- acc
      case (paramSig, argA, argB) of
        (TPS_Ty _, TAType tyA, TAType tyB) ->
          unifyTyFlex tt tmCtx tyFlex tmFlex s tyA tyB
        (TPS_Tm sort, TATm tmA, TATm tmB) ->
          unifyTm tt tmCtx tmFlex s sort tmA tmB
        (TPS_Ty _, _, _) ->
          Left "unifyTyFlex: expected type argument for constructor parameter"
        (TPS_Tm _, _, _) ->
          Left "unifyTyFlex: expected term argument for constructor parameter"

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
  -> S.Set TmVar
  -> Context
  -> Context
  -> Either Text Subst
unifyCtx tt tmCtx tyFlex tmFlex ctx1 ctx2
  | length ctx1 /= length ctx2 = Left "unifyCtx: length mismatch"
  | otherwise =
      foldM
        (\s (a, b) -> unifyTyFlex tt tmCtx tyFlex tmFlex s a b)
        emptySubst
        (zip ctx1 ctx2)

unifyTm
  :: TypeTheory
  -> [TypeExpr]
  -> S.Set TmVar
  -> Subst
  -> TypeExpr
  -> TermDiagram
  -> TermDiagram
  -> Either Text Subst
unifyTm tt tmCtx tmFlex subst expectedSort tm1 tm2 = do
  tmCtxSub <- applySubstCtx tt subst tmCtx
  expectedSort0 <- applySubstTy tt subst expectedSort
  expectedSort' <- normalizeTypeDeepWithCtx tt tmCtxSub expectedSort0
  lhs0 <- applySubstTmInCtx tt tmCtxSub subst expectedSort' tm1
  rhs0 <- applySubstTmInCtx tt tmCtxSub subst expectedSort' tm2
  lhs <- normalizeTermDiagram tt tmCtxSub expectedSort' lhs0
  rhs <- normalizeTermDiagram tt tmCtxSub expectedSort' rhs0
  lhsGraph <- termToDiagram tt tmCtxSub expectedSort' lhs
  rhsGraph <- termToDiagram tt tmCtxSub expectedSort' rhs
  lOut <- requireSingleOut lhsGraph
  rOut <- requireSingleOut rhsGraph
  let lhsInputs = inputGlobalMap lhsGraph
  let rhsInputs = inputGlobalMap rhsGraph
  unifyTmGraph subst S.empty expectedSort' lhsGraph lhsInputs lOut rhsGraph rhsInputs rOut
  where
    normalizeInCtx s ty = do
      tmCtx' <- applySubstCtx tt s tmCtx
      normalizeTypeDeepWithCtx tt tmCtx' ty

    unifyTmGraph s seen currentSort lhsDiag lhsInputs lp rhsDiag rhsInputs rp
      | (lp, rp) `S.member` seen = Right s
      | otherwise = do
          checkPortSort s currentSort lhsDiag lp
          checkPortSort s currentSort rhsDiag rp
          lHead <- classifyPort lhsDiag lhsInputs lp
          rHead <- classifyPort rhsDiag rhsInputs rp
          let seen' = S.insert (lp, rp) seen
          case (lHead, rHead) of
            (PHBound i, PHBound j) -> do
              checkBoundSort s currentSort i
              checkBoundSort s currentSort j
              if i == j
                then Right s
                else Left "unifyTm: bound term-variable mismatch"
            (PHFun f lIns, PHFun g rIns)
              | f == g && length lIns == length rIns -> do
                  sig <- requireFunSigArity s currentSort f (length lIns)
                  foldM
                    (\s1 (argSort, lArg, rArg) -> do
                      argSort0 <- applySubstTy tt s1 argSort
                      tmCtx1 <- applySubstCtx tt s1 tmCtx
                      argSort' <- normalizeTypeDeepWithCtx tt tmCtx1 argSort0
                      unifyTmGraph s1 seen' argSort' lhsDiag lhsInputs lArg rhsDiag rhsInputs rArg
                    )
                    s
                    (zip3 (tfsArgs sig) lIns rIns)
              | otherwise ->
                  Left "unifyTm: function mismatch"
            _ -> do
              lhsTm <- termFromPort lhsDiag lhsInputs lp
              rhsTm <- termFromPort rhsDiag rhsInputs rp
              unifyTmNorm s currentSort lhsTm rhsTm

    unifyTmNorm s currentSort a b =
      case (a, b) of
        (TMBound i, TMBound j) -> do
          checkBoundSort s currentSort i
          checkBoundSort s currentSort j
          if i == j
            then Right s
            else Left "unifyTm: bound term-variable mismatch"
        (TMFun f xs, TMFun g ys)
          | f == g && length xs == length ys -> do
              sig <- requireFunSig s currentSort f xs
              foldl step (Right s) (zip3 (tfsArgs sig) xs ys)
          | otherwise -> Left "unifyTm: function mismatch"
        (TMVar v, TMVar w) -> do
          checkTmVarSort s currentSort v
          checkTmVarSort s currentSort w
          if sameTmVarId v w
            then Right s
            else
              if v `S.member` tmFlex
                then bindTmVar s currentSort v (TMVar w)
                else
                  if w `S.member` tmFlex
                    then bindTmVar s currentSort w (TMVar v)
                    else Left "unifyTm: rigid term variable mismatch"
        (TMVar v, t) -> do
          checkTmVarSort s currentSort v
          ensureTmTermSort s currentSort t
          if v `S.member` tmFlex
            then bindTmVar s currentSort v t
            else Left "unifyTm: rigid term variable mismatch"
        (t, TMVar v) -> do
          checkTmVarSort s currentSort v
          ensureTmTermSort s currentSort t
          if v `S.member` tmFlex
            then bindTmVar s currentSort v t
            else Left "unifyTm: rigid term variable mismatch"
        _ -> Left "unifyTm: cannot unify term expressions"
      where
        step acc (argSort, x, y) = do
          s1 <- acc
          tmCtx1 <- applySubstCtx tt s1 tmCtx
          argSort0 <- applySubstTy tt s1 argSort
          argSort' <- normalizeTypeDeepWithCtx tt tmCtx1 argSort0
          x' <- applySubstExprInCtx tmCtx1 s1 argSort' x
          y' <- applySubstExprInCtx tmCtx1 s1 argSort' y
          xNorm <- normalizeTermExprInCtx tmCtx1 s1 argSort' x'
          yNorm <- normalizeTermExprInCtx tmCtx1 s1 argSort' y'
          unifyTmNorm s1 argSort' xNorm yNorm

    bindTmVar s currentSort v t = do
      sortV0 <- applySubstTy tt s (tmvSort v)
      sortV <- normalizeInCtx s sortV0
      currentSort' <- normalizeInCtx s currentSort
      if sortV /= currentSort'
        then Left "unifyTm: variable sort mismatch"
        else Right ()
      tmCtx' <- applySubstCtx tt s tmCtx
      t' <- applySubstExprInCtx tmCtx' s sortV t
      ensureTmTermSort s sortV t'
      if occursTmVarExpr v t'
        then Left "unifyTm: occurs check failed"
        else do
          let boundSet = boundGlobalsExpr t'
          allowed <- allowedBoundGlobals s sortV v
          if tmvScope v == 0 && not (S.null boundSet)
            then Left "unifyTm: scope-0 metavariable cannot mention bound indices"
            else
              if S.isSubsetOf boundSet allowed
                then do
                  tDiag <- termExprToDiagram tt tmCtx' sortV t'
                  composeSubst tt (Subst M.empty (M.singleton v tDiag)) s
                else Left "unifyTm: escape from bound term-variable scope"

    checkTmVarSort s currentSort v = do
      sortV0 <- applySubstTy tt s (tmvSort v)
      sortV <- normalizeInCtx s sortV0
      currentSort' <- normalizeInCtx s currentSort
      if sortV == currentSort'
        then Right ()
        else Left "unifyTm: term variable sort mismatch"

    checkBoundSort s currentSort i =
      if i < length tmCtx
        then do
          boundSort0 <- applySubstTy tt s (tmCtx !! i)
          boundSort <- normalizeInCtx s boundSort0
          currentSort' <- normalizeInCtx s currentSort
          if boundSort == currentSort'
            then Right ()
            else Left "unifyTm: bound term-variable sort mismatch"
        else Left "unifyTm: bound term-variable out of scope"

    ensureTmTermSort s currentSort tm =
      case tm of
        TMVar v -> checkTmVarSort s currentSort v
        TMBound i -> checkBoundSort s currentSort i
        TMFun f args -> do
          sig <- requireFunSig s currentSort f args
          mapM_ (uncurry (ensureTmTermSort s)) (zip (tfsArgs sig) args)

    requireFunSig s currentSort f args = do
      requireFunSigArity s currentSort f (length args)

    requireFunSigArity s currentSort f arity = do
      currentSort0 <- applySubstTy tt s currentSort
      currentSort' <- normalizeInCtx s currentSort0
      sig <-
        case lookupTmFunSig tt (typeMode currentSort') f of
          Nothing -> Left "unifyTm: unknown term function"
          Just sig' -> Right sig'
      if length (tfsArgs sig) /= arity
        then Left "unifyTm: term function arity mismatch"
        else Right ()
      resSort0 <- applySubstTy tt s (tfsRes sig)
      resSort <- normalizeInCtx s resSort0
      if resSort == currentSort'
        then Right sig
        else Left "unifyTm: term function result sort mismatch"

    applySubstExprInCtx ctx s expectedSort expr =
      go S.empty expectedSort expr
      where
        go seen currentSort tm =
          case tm of
            TMVar v -> do
              sort' <- applySubstTy tt s (tmvSort v)
              let v' = v { tmvSort = sort' }
              case lookupTmById v' (sTm s) of
                Nothing -> Right (TMVar v')
                Just tmSub ->
                  if v' `S.member` seen
                    then Right (TMVar v')
                    else do
                      subExpr <- diagramToTermExpr tt ctx sort' tmSub
                      go (S.insert v' seen) currentSort subExpr
            TMBound _ -> Right tm
            TMFun f args -> do
              sig <- requireFunSigArity s currentSort f (length args)
              args' <- mapM (\(argSort, argTm) -> go seen argSort argTm) (zip (tfsArgs sig) args)
              Right (TMFun f args')

    normalizeTermExprInCtx ctx _ expectedSort expr = do
      tm <- termExprToDiagram tt ctx expectedSort expr
      tmNorm <- normalizeTermDiagram tt ctx expectedSort tm
      diagramToTermExpr tt ctx expectedSort tmNorm

    allowedBoundGlobals s sortV v = do
      sortV' <- normalizeInCtx s sortV
      let mode = typeMode sortV'
      let globals =
            [ i
            | (i, ty) <- zip [0 :: Int ..] tmCtx
            , typeMode ty == mode
            ]
      pure (S.fromList (take (tmvScope v) globals))

    checkPortSort s currentSort diag pid = do
      portSort0 <-
        case diagramPortType diag pid of
          Nothing -> Left "unifyTm: missing port type in normalized term graph"
          Just ty -> Right ty
      portSort <- normalizeInCtx s portSort0
      currentSort' <- normalizeInCtx s currentSort
      if portSort == currentSort'
        then Right ()
        else Left "unifyTm: normalized term graph has unexpected port sort"

    classifyPort diag inputs pid =
      case M.lookup pid inputs of
        Just i -> Right (PHBound i)
        Nothing -> do
          edge <- producerEdge diag pid
          case ePayload edge of
            PGen (GenName fName) attrs bargs
              | M.null attrs && null bargs -> Right (PHFun (TmFunName fName) (eIns edge))
              | otherwise -> Left "unifyTm: non-term generator payload in normalized term graph"
            PTmMeta v -> Right (PHMeta v)
            _ -> Left "unifyTm: non-term payload in normalized term graph"

    termFromPort diag inputs pid = go S.empty pid
      where
        go seen pid0 =
          case M.lookup pid0 inputs of
            Just i -> Right (TMBound i)
            Nothing ->
              if pid0 `S.member` seen
                then Left "unifyTm: cycle detected in normalized term graph"
                else do
                  edge <- producerEdge diag pid0
                  case ePayload edge of
                    PGen (GenName fName) attrs bargs
                      | M.null attrs && null bargs -> do
                          args <- mapM (go (S.insert pid0 seen)) (eIns edge)
                          Right (TMFun (TmFunName fName) args)
                      | otherwise ->
                          Left "unifyTm: non-term generator payload in normalized term graph"
                    PTmMeta v ->
                      Right (TMVar v)
                    _ ->
                      Left "unifyTm: non-term payload in normalized term graph"

    producerEdge diag pid =
      case IM.lookup (unPortId pid) (dProd diag) of
        Just (Just eid) ->
          case IM.lookup (unEdgeId eid) (dEdges diag) of
            Nothing -> Left "unifyTm: producer edge is missing in normalized term graph"
            Just edge -> Right edge
        _ -> Left "unifyTm: missing producer in normalized term graph"

    requireSingleOut diag =
      case dOut diag of
        [pid] -> Right pid
        _ -> Left "unifyTm: normalized term graph must have exactly one output"

    inputGlobalMap diag =
      M.fromList
        [ (pid, resolveGlobal pid local)
        | (local, pid) <- zip [0 :: Int ..] (dIn diag)
        ]
      where
        resolveGlobal pid local =
          case getPortLabel diag pid >>= decodeTmCtxLabel of
            Just globalTm -> globalTm
            Nothing -> local

    decodeTmCtxLabel lbl =
      case T.stripPrefix "tmctx:" lbl of
        Nothing -> Nothing
        Just raw ->
          case reads (T.unpack raw) of
            [(n, "")] -> Just n
            _ -> Nothing

applySubstTy :: TypeTheory -> Subst -> TypeExpr -> Either Text TypeExpr
applySubstTy tt subst ty = do
  raw <- goTy S.empty ty
  if needsTmCtxType raw
    then normalizeTypeExpr (ttModes tt) raw
    else normalizeTypeDeep tt raw
  where
    needsTmCtxType expr =
      case expr of
        TVar _ -> False
        TMod _ inner -> needsTmCtxType inner
        TCon _ args -> any needsTmCtxArg args

    needsTmCtxArg arg =
      case arg of
        TAType innerTy -> needsTmCtxType innerTy
        TATm tm ->
          not (S.null (boundTmIndicesTerm tm)) || maxTmScopeTerm tm > 0

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
        (TPS_Tm sortTy, TATm tmArg) -> do
          sort' <- goTy seen sortTy
          TATm <$> applySubstTmMaybeNormalize tt subst sort' tmArg
        (TPS_Ty _, TATm _) ->
          Left "applySubstTy: expected type argument for constructor parameter"
        (TPS_Tm _, TAType _) ->
          Left "applySubstTy: expected term argument for constructor parameter"

    goArgNoSig seen arg =
      case arg of
        TAType innerTy -> TAType <$> goTy seen innerTy
        TATm tmArg -> do
          sort <- inferTmSortFromDiagram tt subst tmArg
          TATm <$> applySubstTmMaybeNormalize tt subst sort tmArg

applySubstTm :: TypeTheory -> Subst -> TypeExpr -> TermDiagram -> Either Text TermDiagram
applySubstTm tt subst expectedSort tm =
  applySubstTmInCtx tt (dTmCtx (unTerm tm)) subst expectedSort tm

applySubstTmInCtx :: TypeTheory -> [TypeExpr] -> Subst -> TypeExpr -> TermDiagram -> Either Text TermDiagram
applySubstTmInCtx tt tmCtx subst expectedSort tm = do
  tmCtx' <- applySubstCtx tt subst tmCtx
  expectedSort0 <- applySubstTy tt subst expectedSort
  expectedSort' <- normalizeTypeDeepWithCtx tt tmCtx' expectedSort0
  tmGraph <- Diag.applySubstDiagram tt subst (unTerm tm)
  let tmSub = TermDiagram tmGraph
  expr <- diagramToTermExpr tt tmCtx' expectedSort' tmSub
  (tmCtxOut, expr') <- goTm S.empty tmCtx' expectedSort' expr
  expectedSortOut <- normalizeTypeDeepWithCtx tt tmCtxOut expectedSort0
  tm' <- termExprToDiagram tt tmCtxOut expectedSortOut expr'
  normalizeTermDiagram tt tmCtxOut expectedSortOut tm'
  where
    goTm seen curCtx currentSort expr =
      case expr of
        TMVar v -> do
          sort' <- applySubstTy tt subst (tmvSort v)
          let v' = v { tmvSort = sort' }
          case lookupTmById v' (sTm subst) of
            Nothing -> Right (curCtx, TMVar v')
            Just tmSub ->
              if v' `S.member` seen
                then Right (curCtx, TMVar v')
                else do
                  subCtx0 <- applySubstCtx tt subst (dTmCtx (unTerm tmSub))
                  sortSub <- normalizeTypeDeepWithCtx tt subCtx0 sort'
                  subExpr <- diagramToTermExpr tt subCtx0 sortSub tmSub
                  (subCtx, subExpr') <- goTm (S.insert v' seen) subCtx0 currentSort subExpr
                  merged <- mergeCtx curCtx subCtx
                  Right (merged, subExpr')
        TMBound _ -> Right (curCtx, expr)
        TMFun name args -> do
          sig <- requireSig curCtx currentSort name (length args)
          (ctxOut, argsRev) <-
            foldM
              (\(ctxAcc, acc) (argSort, argTm) -> do
                argSort' <- normalizeTypeDeepWithCtx tt ctxAcc =<< applySubstTy tt subst argSort
                (ctxArg, argExpr) <- goTm seen ctxAcc argSort' argTm
                ctxNext <- mergeCtx ctxAcc ctxArg
                Right (ctxNext, argExpr : acc))
              (curCtx, [])
              (zip (tfsArgs sig) args)
          Right (ctxOut, TMFun name (reverse argsRev))

    requireSig curCtx currentSort f arity = do
      currentSort' <- normalizeTypeDeepWithCtx tt curCtx =<< applySubstTy tt subst currentSort
      sig <-
        case lookupTmFunSig tt (typeMode currentSort') f of
          Nothing -> Left "applySubstTmInCtx: unknown term function"
          Just s -> Right s
      if length (tfsArgs sig) == arity
        then Right sig
        else Left "applySubstTmInCtx: term function arity mismatch"

    mergeCtx left right =
      let maxLen = max (length left) (length right)
      in mapM pick [0 :: Int .. maxLen - 1]
      where
        pick i =
          case (nth left i, nth right i) of
            (Just a, Just b) ->
              if a == b
                then Right a
                else Left "applySubstTmInCtx: incompatible term contexts during substitution"
            (Just a, Nothing) -> Right a
            (Nothing, Just b) -> Right b
            (Nothing, Nothing) -> Left "applySubstTmInCtx: internal context merge failure"

applySubstCtx :: TypeTheory -> Subst -> Context -> Either Text Context
applySubstCtx tt subst = mapM (applySubstTy tt subst)

normalizeSubst :: TypeTheory -> Subst -> Either Text Subst
normalizeSubst tt subst = do
  tyPairs <- mapM normTy (M.toList (sTy subst))
  tmPairs <- mapM normTm (M.toList (sTm subst))
  let tyMap = M.fromList [ (v, t) | (v, t) <- tyPairs, t /= TVar v ]
  let tmMap = M.fromList [ (v, t) | (v, t) <- tmPairs, not (isTmIdentity v t) ]
  Right (Subst tyMap tmMap)
  where
    normTy (v, t) = do
      t' <- applySubstTy tt subst t
      pure (v, t')
    normTm (v, t) = do
      sort' <- applySubstTy tt subst (tmvSort v)
      t' <- applySubstTmMaybeNormalize tt subst sort' t
      pure (v { tmvSort = sort' }, t')

composeSubst :: TypeTheory -> Subst -> Subst -> Either Text Subst
composeSubst tt s2 s1 = do
  ty1' <- mapM (applySubstTy tt s2) (sTy s1)
  tm1' <- fmap M.fromList (mapM substTmPair (M.toList (sTm s1)))
  normalizeSubst tt (Subst (M.union ty1' (sTy s2)) (M.union tm1' (sTm s2)))
  where
    substTmPair (v, t) = do
      sort' <- applySubstTy tt s2 (tmvSort v)
      t' <- applySubstTmMaybeNormalize tt s2 sort' t
      pure (v { tmvSort = sort' }, t')

applySubstTmMaybeNormalize :: TypeTheory -> Subst -> TypeExpr -> TermDiagram -> Either Text TermDiagram
applySubstTmMaybeNormalize tt subst expectedSort tm =
  if S.null (boundTmIndicesTerm tm) && maxTmScopeTerm tm == 0
    then applySubstTm tt subst expectedSort tm
    else applySubstTmNoNormalize tt subst expectedSort tm

applySubstTmNoNormalize :: TypeTheory -> Subst -> TypeExpr -> TermDiagram -> Either Text TermDiagram
applySubstTmNoNormalize tt subst expectedSort tm = do
  tmGraph <- Diag.applySubstDiagram tt subst (unTerm tm)
  let tmSub = TermDiagram tmGraph
  let tmCtx = dTmCtx (unTerm tmSub)
  expectedSort0 <- applySubstTy tt subst expectedSort
  expectedSort' <- normalizeTypeDeepWithCtx tt tmCtx expectedSort0
  expr <- diagramToTermExpr tt tmCtx expectedSort' tmSub
  (tmCtxOut, expr') <- go S.empty tmCtx expectedSort' expr
  expectedSortOut <- normalizeTypeDeepWithCtx tt tmCtxOut expectedSort0
  termExprToDiagram tt tmCtxOut expectedSortOut expr'
  where
    go seen curCtx currentSort expr =
      case expr of
        TMVar v -> do
          sort' <- applySubstTy tt subst (tmvSort v)
          let v' = v { tmvSort = sort' }
          case lookupTmById v' (sTm subst) of
            Nothing -> Right (curCtx, TMVar v')
            Just tmSub ->
              if v' `S.member` seen
                then Right (curCtx, TMVar v')
                else do
                  subCtx0 <- applySubstCtx tt subst (dTmCtx (unTerm tmSub))
                  sortSub <- normalizeTypeDeepWithCtx tt subCtx0 sort'
                  subExpr <- diagramToTermExpr tt subCtx0 sortSub tmSub
                  (subCtx, subExpr') <- go (S.insert v' seen) subCtx0 currentSort subExpr
                  merged <- mergeCtx curCtx subCtx
                  Right (merged, subExpr')
        TMBound _ -> Right (curCtx, expr)
        TMFun f args -> do
          sig <- requireSig curCtx currentSort f (length args)
          (ctxOut, argsRev) <-
            foldM
              (\(ctxAcc, acc) (argSort, argTm) -> do
                argSort' <- normalizeTypeDeepWithCtx tt ctxAcc =<< applySubstTy tt subst argSort
                (ctxArg, argExpr) <- go seen ctxAcc argSort' argTm
                ctxNext <- mergeCtx ctxAcc ctxArg
                Right (ctxNext, argExpr : acc))
              (curCtx, [])
              (zip (tfsArgs sig) args)
          Right (ctxOut, TMFun f (reverse argsRev))

    requireSig curCtx currentSort f arity = do
      currentSort' <- normalizeTypeDeepWithCtx tt curCtx =<< applySubstTy tt subst currentSort
      sig <-
        case lookupTmFunSig tt (typeMode currentSort') f of
          Nothing -> Left "applySubstTmNoNormalize: unknown term function"
          Just s -> Right s
      if length (tfsArgs sig) == arity
        then Right sig
        else Left "applySubstTmNoNormalize: term function arity mismatch"

    mergeCtx left right =
      let maxLen = max (length left) (length right)
      in mapM pick [0 :: Int .. maxLen - 1]
      where
        pick i =
          case (nth left i, nth right i) of
            (Just a, Just b) ->
              if a == b
                then Right a
                else Left "applySubstTmNoNormalize: incompatible term contexts during substitution"
            (Just a, Nothing) -> Right a
            (Nothing, Just b) -> Right b
            (Nothing, Nothing) -> Left "applySubstTmNoNormalize: internal context merge failure"

maxTmScopeTerm :: TermDiagram -> Int
maxTmScopeTerm tm =
  maximum
    ( 0
        : [ tmvScope v
          | edge <- IM.elems (dEdges (unTerm tm))
          , PTmMeta v <- [ePayload edge]
          ]
    )

inferExpectedTmSort :: TypeTheory -> [TypeExpr] -> Subst -> TermDiagram -> TermDiagram -> Either Text TypeExpr
inferExpectedTmSort tt tmCtx subst lhs rhs =
  case inferTmSortFromTerm tt tmCtx subst lhs of
    Right ty -> Right ty
    Left _ -> inferTmSortFromTerm tt tmCtx subst rhs

inferTmSortFromTerm :: TypeTheory -> [TypeExpr] -> Subst -> TermDiagram -> Either Text TypeExpr
inferTmSortFromTerm tt _ixCtx subst tm =
  inferTmSortFromDiagram tt subst tm

inferTmSortFromDiagram :: TypeTheory -> Subst -> TermDiagram -> Either Text TypeExpr
inferTmSortFromDiagram tt subst tm =
  case dOut (unTerm tm) of
    [pid] ->
      case diagramPortType (unTerm tm) pid of
        Nothing -> Left "inferTmSortFromDiagram: missing output port type"
        Just ty -> applySubstTy tt subst ty
    _ -> Left "inferTmSortFromDiagram: term diagram must have exactly one output"

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
        TATm tmArg -> any (occursTyVar v . tmvSort) (S.toList (freeTmVarsTerm tmArg))

occursTmVarExpr :: TmVar -> TermExpr -> Bool
occursTmVarExpr v tm =
  case tm of
    TMVar v' -> sameTmVarId v v'
    TMBound _ -> False
    TMFun _ args -> any (occursTmVarExpr v) args

sameTmVarId :: TmVar -> TmVar -> Bool
sameTmVarId a b = tmvName a == tmvName b && tmvScope a == tmvScope b

lookupTmById :: TmVar -> M.Map TmVar TermDiagram -> Maybe TermDiagram
lookupTmById v mp =
  case M.lookup v mp of
    Just tm -> Just tm
    Nothing ->
      snd <$> findTmById (M.toList mp)
  where
    findTmById [] = Nothing
    findTmById ((k, tm):rest)
      | sameTmVarId k v = Just (k, tm)
      | otherwise = findTmById rest

isTmIdentity :: TmVar -> TermDiagram -> Bool
isTmIdentity v tm =
  case IM.elems (dEdges (unTerm tm)) of
    [edge] ->
      case (ePayload edge, eIns edge, eOuts edge, dIn (unTerm tm), dOut (unTerm tm)) of
        (PTmMeta w, [], [outPid], [], [outBoundary]) ->
          outPid == outBoundary && sameTmVarId v w
        _ -> False
    _ -> False

nth :: [a] -> Int -> Maybe a
nth xs i
  | i < 0 = Nothing
  | otherwise =
      case drop i xs of
        (y:_) -> Just y
        [] -> Nothing

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
        TATm _ -> "<tm>"

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
