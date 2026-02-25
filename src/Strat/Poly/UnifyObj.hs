{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.UnifyObj
  ( MetaRhs(..)
  , Subst(..)
  , mkSubst
  , lookupCodeMeta
  , lookupTmMeta
  , insertCodeMeta
  , insertTmMeta
  , codeBindings
  , tmBindings
  , emptySubst
  , unifyObj
  , unifyObjFlex
  , unifyTm
  , unifyCtx
  , diagramTmCtx
  , unifyCtxDiagram
  , applySubstObj
  , applySubstTm
  , applySubstDiagram
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
import Strat.Poly.ModeTheory (ModeName(..), ModName(..), ModExpr(..), ModDecl(..), ModeTheory(..))
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Obj
import Strat.Poly.ObjClassifier (modeClassifierMode)
import Strat.Poly.Graph
  ( Diagram(..)
  , Edge(..)
  , EdgePayload(..)
  , PortId(..)
  , diagramPortObj
  , weakenDiagramTmCtxTo
  , unPortId
  , unEdgeId
  )
import Strat.Poly.TypeTheory
  ( TypeTheory(..)
  , TypeParamSig(..)
  , TmFunSig(..)
  , lookupTmFunSig
  )
import Strat.Poly.Traversal (traverseDiagram)
import Strat.Poly.DefEq
  ( normalizeObjDeep
  , normalizeObjDeepWithCtx
  , normalizeTermDiagram
  , termToDiagram
  )
import Strat.Poly.TermExpr
  ( TermExpr(..)
  , diagramToTermExpr
  , termExprToDiagram
  , boundGlobalsExpr
  )


data MetaRhs
  = MRCode Obj
  | MRTm TermDiagram
  deriving (Eq, Ord, Show)

newtype Subst = Subst
  { sMeta :: M.Map TmVar MetaRhs
  } deriving (Eq, Ord, Show)

data PortHead
  = PHBound Int
  | PHFun TmFunName [PortId]
  | PHMeta TmVar

lookupCodeMeta :: Subst -> TmVar -> Maybe Obj
lookupCodeMeta subst v =
  case M.lookup v (sMeta subst) of
    Just (MRCode t) -> Just t
    _ -> Nothing

lookupTmMeta :: Subst -> TmVar -> Maybe TermDiagram
lookupTmMeta subst v =
  case M.lookup v (sMeta subst) of
    Just (MRTm tm) -> Just tm
    _ -> Nothing

codeBindings :: Subst -> [(TmVar, Obj)]
codeBindings subst =
  [ (v, t)
  | (v, rhs) <- M.toList (sMeta subst)
  , MRCode t <- [rhs]
  ]

tmBindings :: Subst -> [(TmVar, TermDiagram)]
tmBindings subst =
  [ (v, tm)
  | (v, rhs) <- M.toList (sMeta subst)
  , MRTm tm <- [rhs]
  ]

insertCodeMeta :: TmVar -> Obj -> Subst -> Either Text Subst
insertCodeMeta v t subst =
  case M.lookup v (sMeta subst) of
        Just (MRTm _) -> Left "subst: metavariable kind mismatch (code vs term)"
        _ -> Right subst { sMeta = M.insert v (MRCode t) (sMeta subst) }

insertTmMeta :: TmVar -> TermDiagram -> Subst -> Either Text Subst
insertTmMeta v tm subst =
  case M.lookup v (sMeta subst) of
    Just (MRCode _) -> Left "subst: metavariable kind mismatch (term vs code)"
    _ -> Right subst { sMeta = M.insert v (MRTm tm) (sMeta subst) }

mkSubst :: M.Map TmVar Obj -> M.Map TmVar TermDiagram -> Subst
mkSubst objMap tmMap =
  case foldM addObj (Subst M.empty) (M.toList objMap) >>= \s -> foldM addTm s (M.toList tmMap) of
    Left err -> error (T.unpack err)
    Right s -> s
  where
    addObj s (v, t) = insertCodeMeta v t s
    addTm s (v, tm) = insertTmMeta v tm s

sObj :: Subst -> M.Map TmVar Obj
sObj = M.fromList . codeBindings

sTm :: Subst -> M.Map TmVar TermDiagram
sTm = M.fromList . tmBindings

emptySubst :: Subst
emptySubst = Subst M.empty

unifyObj :: TypeTheory -> Obj -> Obj -> Either Text Subst
unifyObj tt t1 t2 =
  let flex = S.union (freeObjVarsObj t1) (freeTmVarsObj t1)
      flex' = S.union flex (S.union (freeObjVarsObj t2) (freeTmVarsObj t2))
   in unifyObjFlex tt [] flex' emptySubst t1 t2

unifyObjFlex
  :: TypeTheory
  -> [Obj]
  -> S.Set TmVar
  -> Subst
  -> Obj
  -> Obj
  -> Either Text Subst
unifyObjFlex tt tmCtx flex subst t1 t2 = do
  t1' <- applySubstObj tt subst t1 >>= expandModSpine
  t2' <- applySubstObj tt subst t2 >>= expandModSpine
  unifyWith subst t1' t2'
  where
    mkObj owner code = Obj { objOwnerMode = owner, objCode = code }

    objVarObj v = OVar v

    expandModSpine ty =
      case objCode ty of
        CTMeta _ -> Right ty
        CTCon ref args -> do
          args' <- mapM expandArg args
          Right ty { objCode = CTCon ref args' }
        CTMod me innerCode -> do
          if objOwnerMode ty == meTgt me
            then Right ()
            else Left "unifyObjFlex: modality target does not match object owner mode in CTMod spine"
          inner' <- expandModSpine (mkObj (meSrc me) innerCode)
          code' <- expandPath CTMod True me (objCode inner')
          Right ty { objCode = code' }
        CTLift me innerCode -> do
          if modeClassifierMode (ttModes tt) (objOwnerMode ty) == meTgt me
            then Right ()
            else Left "unifyObjFlex: lift target does not match object owner mode in CTLift spine"
          inner' <- expandModSpine (mkObj (meSrc me) innerCode)
          code' <- expandPath CTLift False me (objCode inner')
          Right ty { objCode = code' }

    expandArg arg =
      case arg of
        CAObj ty -> CAObj <$> expandModSpine ty
        CATm tm -> Right (CATm tm)

    expandPath wrap dropIdentity me innerCode =
      case mePath me of
        [] ->
          if meSrc me == meTgt me
            then
              if dropIdentity
                then Right innerCode
                else Right (wrap me innerCode)
            else Left "unifyObjFlex: ill-typed empty modality path"
        _ -> do
          (cur, outCode) <- foldM step (meSrc me, innerCode) (mePath me)
          if cur == meTgt me
            then Right outCode
            else Left "unifyObjFlex: ill-typed modality path"
      where
        step (cur, acc) name =
          case M.lookup name (mtDecls (ttModes tt)) of
            Nothing -> Left "unifyObjFlex: unknown modality in type"
            Just decl ->
              if mdSrc decl == cur
                then
                  Right
                    ( mdTgt decl
                    , wrap
                        ModExpr
                          { meSrc = mdSrc decl
                          , meTgt = mdTgt decl
                          , mePath = [name]
                          }
                        acc
                    )
                else Left "unifyObjFlex: ill-typed modality path"

    unifyWith s a b =
      if objOwnerMode a /= objOwnerMode b
        then Left ("unifyObjFlex: owner-mode mismatch " <> renderObj a <> " with " <> renderObj b)
        else unifyCode s (objOwnerMode a) (objCode a) (objCode b)

    unifyCode s owner codeA codeB =
      case (codeA, codeB) of
        (CTMeta v, CTMeta w) -> unifyTyVar s v (objVarObj w)
        (CTMeta v, t) -> unifyTyVar s v (mkObj owner t)
        (t, CTMeta v) -> unifyTyVar s v (mkObj owner t)
        (CTCon refA argsA, CTCon refB argsB)
          | refA == refB && length argsA == length argsB ->
              case M.lookup refA (ttObjParams tt) of
                Just params
                  | length params == length argsA ->
                      foldl stepBySig (Right s) (zip params (zip argsA argsB))
                _ ->
                  foldl step (Right s) (zip argsA argsB)
          | otherwise ->
              Left ("unifyObjFlex: cannot unify " <> renderObj (mkObj owner codeA) <> " with " <> renderObj (mkObj owner codeB))
        (CTMod me1 innerA, CTMod me2 innerB)
          | me1 == me2 ->
              unifyCode s (meSrc me1) innerA innerB
          | otherwise ->
              Left ("unifyObjFlex: cannot unify " <> renderObj (mkObj owner codeA) <> " with " <> renderObj (mkObj owner codeB))
        (CTLift me1 innerA, CTLift me2 innerB)
          | me1 == me2 ->
              unifyCode s (meSrc me1) innerA innerB
          | otherwise ->
              Left ("unifyObjFlex: cannot unify " <> renderObj (mkObj owner codeA) <> " with " <> renderObj (mkObj owner codeB))
        _ ->
          Left ("unifyObjFlex: cannot unify " <> renderObj (mkObj owner codeA) <> " with " <> renderObj (mkObj owner codeB))

    step acc (argA, argB) = do
      s <- acc
      case (argA, argB) of
        (CAObj tyA, CAObj tyB) ->
          unifyObjFlex tt tmCtx flex s tyA tyB
        (CATm tmA, CATm tmB) -> do
          sort <- inferExpectedTmSort tt tmCtx s tmA tmB
          unifyTm tt tmCtx flex s sort tmA tmB
        _ -> Left "unifyObjFlex: mixed type/term arguments cannot unify"

    stepBySig acc (paramSig, (argA, argB)) = do
      s <- acc
      case (paramSig, argA, argB) of
        (TPS_Ty _, CAObj tyA, CAObj tyB) ->
          unifyObjFlex tt tmCtx flex s tyA tyB
        (TPS_Tm sort, CATm tmA, CATm tmB) ->
          unifyTm tt tmCtx flex s sort tmA tmB
        (TPS_Ty _, _, _) ->
          Left "unifyObjFlex: expected type argument for constructor parameter"
        (TPS_Tm _, _, _) ->
          Left "unifyObjFlex: expected term argument for constructor parameter"

    unifyTyVar s v t
      | v `S.member` flex = bindTyVar s v t
      | otherwise =
          case objCode t of
            CTMeta v' | v == v' -> Right s
            CTMeta v' | v' `S.member` flex -> bindTyVar s v' (objVarObj v)
            _ -> Left ("unifyObjFlex: rigid variable mismatch " <> renderObjVar v <> " with " <> renderObj t)

    bindTyVar s v t = do
      t' <- applySubstObj tt s t
      tmCtx' <- applySubstCtx tt s tmCtx
      sortV <- normalizeObjDeepWithCtx tt tmCtx' =<< applySubstObj tt s (tmvSort v)
      let ownerV =
            case tmvOwnerMode v of
              Just owner -> owner
              Nothing -> objOwnerMode sortV
      let scopeMode = modeClassifierMode (ttModes tt) ownerV
      if ownerV /= objOwnerMode t'
        then Left ("unifyObjFlex: mode mismatch " <> renderObjVar v <> " with " <> renderObj t')
        else if t' == objVarObj v
          then Right s
        else if occursObjVar v t'
            then Left ("unifyObjFlex: occurs check failed for " <> renderObjVar v <> " in " <> renderObj t')
            else do
              let boundSet = boundTmIndicesObj t'
                  allowed =
                    S.fromList
                      ( take
                          (tmvScope v)
                          [ i
                          | (i, tyCtx) <- zip [0 :: Int ..] tmCtx'
                          , objOwnerMode tyCtx == scopeMode
                          ]
                      )
              if tmvScope v == 0 && not (S.null boundSet)
                then Left "unifyObjFlex: scope-0 code metavariable cannot mention bound indices"
                else
                  if S.isSubsetOf boundSet allowed
                    then composeSubst tt (mkSubst (M.singleton v t') M.empty) s
                    else Left "unifyObjFlex: escape from bound term-variable scope in code metavariable binding"

unifyCtx
  :: TypeTheory
  -> [Obj]
  -> S.Set TmVar
  -> Context
  -> Context
  -> Either Text Subst
unifyCtx tt tmCtx flex ctx1 ctx2
  | length ctx1 /= length ctx2 = Left "unifyCtx: length mismatch"
  | otherwise =
      foldM
        (\s (a, b) -> unifyObjFlex tt tmCtx flex s a b)
        emptySubst
        (zip ctx1 ctx2)

diagramTmCtx :: Diagram -> [Obj]
diagramTmCtx = dTmCtx

unifyCtxDiagram
  :: TypeTheory
  -> Diagram
  -> S.Set TmVar
  -> Context
  -> Context
  -> Either Text Subst
unifyCtxDiagram tt diag flex =
  unifyCtx tt (diagramTmCtx diag) flex

unifyTm
  :: TypeTheory
  -> [Obj]
  -> S.Set TmVar
  -> Subst
  -> Obj
  -> TermDiagram
  -> TermDiagram
  -> Either Text Subst
unifyTm tt tmCtx tmFlex subst expectedSort tm1 tm2 = do
  tmCtxSub <- applySubstCtx tt subst tmCtx
  expectedSort0 <- applySubstObj tt subst expectedSort
  expectedSort' <- normalizeObjDeepWithCtx tt tmCtxSub expectedSort0
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
      normalizeObjDeepWithCtx tt tmCtx' ty

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
                      argSort0 <- applySubstObj tt s1 argSort
                      tmCtx1 <- applySubstCtx tt s1 tmCtx
                      argSort' <- normalizeObjDeepWithCtx tt tmCtx1 argSort0
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
          argSort0 <- applySubstObj tt s1 argSort
          argSort' <- normalizeObjDeepWithCtx tt tmCtx1 argSort0
          x' <- applySubstExprInCtx tmCtx1 s1 argSort' x
          y' <- applySubstExprInCtx tmCtx1 s1 argSort' y
          xNorm <- normalizeTermExprInCtx tmCtx1 s1 argSort' x'
          yNorm <- normalizeTermExprInCtx tmCtx1 s1 argSort' y'
          unifyTmNorm s1 argSort' xNorm yNorm

    bindTmVar s currentSort v t = do
      sortV0 <- applySubstObj tt s (tmvSort v)
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
                  composeSubst tt (mkSubst M.empty (M.singleton v tDiag)) s
                else Left "unifyTm: escape from bound term-variable scope"

    checkTmVarSort s currentSort v = do
      sortV0 <- applySubstObj tt s (tmvSort v)
      sortV <- normalizeInCtx s sortV0
      currentSort' <- normalizeInCtx s currentSort
      if sortV == currentSort'
        then Right ()
        else Left "unifyTm: term variable sort mismatch"

    checkBoundSort s currentSort i =
      if i < length tmCtx
        then do
          boundSort0 <- applySubstObj tt s (tmCtx !! i)
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
      currentSort0 <- applySubstObj tt s currentSort
      currentSort' <- normalizeInCtx s currentSort0
      sig <-
        case lookupTmFunSig tt (objOwnerMode currentSort') f of
          Nothing -> Left "unifyTm: unknown term function"
          Just sig' -> Right sig'
      if length (tfsArgs sig) /= arity
        then Left "unifyTm: term function arity mismatch"
        else Right ()
      resSort0 <- applySubstObj tt s (tfsRes sig)
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
              sort' <- applySubstObj tt s (tmvSort v)
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
      let mode = objOwnerMode sortV'
      let globals =
            [ i
            | (i, ty) <- zip [0 :: Int ..] tmCtx
            , objOwnerMode ty == mode
            ]
      pure (S.fromList (take (tmvScope v) globals))

    checkPortSort s currentSort diag pid = do
      portSort0 <-
        case diagramPortObj diag pid of
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
        [ (pid, globalTm)
        | (local, pid) <- zip [0 :: Int ..] (dIn diag)
        , Just globalTm <- [resolveTmCtxIndex tmCtx (dMode diag) local]
        ]

applySubstObj :: TypeTheory -> Subst -> Obj -> Either Text Obj
applySubstObj tt subst ty = do
  raw <- goTy S.empty ty
  if needsTmCtxType raw
    then normalizeObjExpr (ttModes tt) raw
    else normalizeObjDeep tt raw
  where
    mkObj owner code = Obj { objOwnerMode = owner, objCode = code }

    needsTmCtxType expr =
      case objCode expr of
        CTMeta _ -> False
        CTMod me innerCode -> needsTmCtxType (mkObj (meSrc me) innerCode)
        CTLift me innerCode -> needsTmCtxType (mkObj (meSrc me) innerCode)
        CTCon _ args -> any needsTmCtxArg args

    needsTmCtxArg arg =
      case arg of
        CAObj innerTy -> needsTmCtxType innerTy
        CATm tm ->
          not (S.null (boundTmIndicesTerm tm)) || maxTmScopeTerm tm > 0

    goTy seen expr =
      case objCode expr of
        CTMeta v ->
          case lookupCodeMeta subst v of
            Nothing -> Right expr
            Just t ->
              if v `S.member` seen
                then Right expr
                else goTy (S.insert v seen) t
        CTCon ref args -> do
          args' <-
            case M.lookup ref (ttObjParams tt) of
              Just params ->
                if length params /= length args
                  then Left "applySubstObj: type constructor arity mismatch"
                  else mapM (goArgBySig seen) (zip params args)
              Nothing ->
                mapM (goArgNoSig seen) args
          Right expr { objCode = CTCon ref args' }
        CTMod me innerCode -> do
          inner' <- goTy seen (mkObj (meSrc me) innerCode)
          Right expr { objCode = CTMod me (objCode inner') }
        CTLift me innerCode -> do
          inner' <- goTy seen (mkObj (meSrc me) innerCode)
          Right expr { objCode = CTLift me (objCode inner') }

    goArgBySig seen (param, arg) =
      case (param, arg) of
        (TPS_Ty _, CAObj innerTy) ->
          CAObj <$> goTy seen innerTy
        (TPS_Tm sortTy, CATm tmArg) -> do
          sort' <- goTy seen sortTy
          CATm <$> applySubstTmMaybeNormalize tt subst sort' tmArg
        (TPS_Ty _, CATm _) ->
          Left "applySubstObj: expected type argument for constructor parameter"
        (TPS_Tm _, CAObj _) ->
          Left "applySubstObj: expected term argument for constructor parameter"

    goArgNoSig seen arg =
      case arg of
        CAObj innerTy -> CAObj <$> goTy seen innerTy
        CATm tmArg -> do
          sort <- inferTmSortFromDiagram tt subst tmArg
          CATm <$> applySubstTmMaybeNormalize tt subst sort tmArg

applySubstTm :: TypeTheory -> Subst -> Obj -> TermDiagram -> Either Text TermDiagram
applySubstTm tt subst expectedSort tm =
  applySubstTmInCtx tt (dTmCtx (unTerm tm)) subst expectedSort tm

applySubstDiagram :: TypeTheory -> Subst -> Diagram -> Either Text Diagram
applySubstDiagram tt subst =
  traverseDiagram onDiag onPayload pure
  where
    onDiag d = do
      dPortObj' <- IM.traverseWithKey (\_ ty -> applySubstObj tt subst ty) (dPortObj d)
      dTmCtx' <- mapM (applySubstObj tt subst) (dTmCtx d)
      pure d { dTmCtx = dTmCtx', dPortObj = dPortObj' }
    onPayload payload =
      case payload of
        PTmMeta v -> do
          sort' <- applySubstObj tt subst (tmvSort v)
          pure (PTmMeta v { tmvSort = sort' })
        _ -> pure payload

applySubstTmInCtx :: TypeTheory -> [Obj] -> Subst -> Obj -> TermDiagram -> Either Text TermDiagram
applySubstTmInCtx tt tmCtx subst expectedSort tm = do
  tmCtx' <- applySubstCtx tt subst tmCtx
  expectedSort0 <- applySubstObj tt subst expectedSort
  expectedSort' <- normalizeObjDeepWithCtx tt tmCtx' expectedSort0
  tmGraph0 <- applySubstDiagram tt subst (unTerm tm)
  tmGraph <- weakenDiagramTmCtxTo tmCtx' tmGraph0
  let tmSub = TermDiagram tmGraph
  expr <- diagramToTermExpr tt tmCtx' expectedSort' tmSub
  (tmCtxOut, expr') <- goTm S.empty tmCtx' expectedSort' expr
  expectedSortOut <- normalizeObjDeepWithCtx tt tmCtxOut expectedSort0
  tm' <- termExprToDiagram tt tmCtxOut expectedSortOut expr'
  normalizeTermDiagram tt tmCtxOut expectedSortOut tm'
  where
    goTm seen curCtx currentSort expr =
      case expr of
        TMVar v -> do
          sort' <- applySubstObj tt subst (tmvSort v)
          let v' = v { tmvSort = sort' }
          case lookupTmById v' (sTm subst) of
            Nothing -> Right (curCtx, TMVar v')
            Just tmSub ->
              if v' `S.member` seen
                then Right (curCtx, TMVar v')
                else do
                  subCtx0 <- applySubstCtx tt subst (dTmCtx (unTerm tmSub))
                  sortSub <- normalizeObjDeepWithCtx tt subCtx0 sort'
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
                argSort' <- normalizeObjDeepWithCtx tt ctxAcc =<< applySubstObj tt subst argSort
                (ctxArg, argExpr) <- goTm seen ctxAcc argSort' argTm
                ctxNext <- mergeCtx ctxAcc ctxArg
                Right (ctxNext, argExpr : acc))
              (curCtx, [])
              (zip (tfsArgs sig) args)
          Right (ctxOut, TMFun name (reverse argsRev))

    requireSig curCtx currentSort f arity = do
      currentSort' <- normalizeObjDeepWithCtx tt curCtx =<< applySubstObj tt subst currentSort
      sig <-
        case lookupTmFunSig tt (objOwnerMode currentSort') f of
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
applySubstCtx tt subst = mapM (applySubstObj tt subst)

normalizeSubst :: TypeTheory -> Subst -> Either Text Subst
normalizeSubst tt subst = do
  tyPairs <- mapM normTy (M.toList (sObj subst))
  tmPairs <- mapM normTm (M.toList (sTm subst))
  let tyMap = M.fromList [ (v, t) | (v, t) <- tyPairs, t /= OVar v ]
  let tmMap = M.fromList [ (v, t) | (v, t) <- tmPairs, not (isTmIdentity v t) ]
  Right (mkSubst tyMap tmMap)
  where
    normTy (v, t) = do
      t' <- applySubstObj tt subst t
      pure (v, t')
    normTm (v, t) = do
      sort' <- applySubstObj tt subst (tmvSort v)
      t' <- applySubstTmMaybeNormalize tt subst sort' t
      pure (v { tmvSort = sort' }, t')

composeSubst :: TypeTheory -> Subst -> Subst -> Either Text Subst
composeSubst tt s2 s1 = do
  ty1' <- mapM (applySubstObj tt s2) (sObj s1)
  tm1' <- fmap M.fromList (mapM substTmPair (M.toList (sTm s1)))
  normalizeSubst tt (mkSubst (M.union ty1' (sObj s2)) (M.union tm1' (sTm s2)))
  where
    substTmPair (v, t) = do
      sort' <- applySubstObj tt s2 (tmvSort v)
      t' <- applySubstTmMaybeNormalize tt s2 sort' t
      pure (v { tmvSort = sort' }, t')

applySubstTmMaybeNormalize :: TypeTheory -> Subst -> Obj -> TermDiagram -> Either Text TermDiagram
applySubstTmMaybeNormalize tt subst expectedSort tm =
  if S.null (boundTmIndicesTerm tm) && maxTmScopeTerm tm == 0
    then applySubstTm tt subst expectedSort tm
    else applySubstTmNoNormalize tt subst expectedSort tm

applySubstTmNoNormalize :: TypeTheory -> Subst -> Obj -> TermDiagram -> Either Text TermDiagram
applySubstTmNoNormalize tt subst expectedSort tm = do
  tmGraph <- applySubstDiagram tt subst (unTerm tm)
  let tmSub = TermDiagram tmGraph
  let tmCtx = dTmCtx (unTerm tmSub)
  expectedSort0 <- applySubstObj tt subst expectedSort
  expectedSort' <- normalizeObjDeepWithCtx tt tmCtx expectedSort0
  expr <- diagramToTermExpr tt tmCtx expectedSort' tmSub
  (tmCtxOut, expr') <- go S.empty tmCtx expectedSort' expr
  expectedSortOut <- normalizeObjDeepWithCtx tt tmCtxOut expectedSort0
  termExprToDiagram tt tmCtxOut expectedSortOut expr'
  where
    go seen curCtx currentSort expr =
      case expr of
        TMVar v -> do
          sort' <- applySubstObj tt subst (tmvSort v)
          let v' = v { tmvSort = sort' }
          case lookupTmById v' (sTm subst) of
            Nothing -> Right (curCtx, TMVar v')
            Just tmSub ->
              if v' `S.member` seen
                then Right (curCtx, TMVar v')
                else do
                  subCtx0 <- applySubstCtx tt subst (dTmCtx (unTerm tmSub))
                  sortSub <- normalizeObjDeepWithCtx tt subCtx0 sort'
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
                argSort' <- normalizeObjDeepWithCtx tt ctxAcc =<< applySubstObj tt subst argSort
                (ctxArg, argExpr) <- go seen ctxAcc argSort' argTm
                ctxNext <- mergeCtx ctxAcc ctxArg
                Right (ctxNext, argExpr : acc))
              (curCtx, [])
              (zip (tfsArgs sig) args)
          Right (ctxOut, TMFun f (reverse argsRev))

    requireSig curCtx currentSort f arity = do
      currentSort' <- normalizeObjDeepWithCtx tt curCtx =<< applySubstObj tt subst currentSort
      sig <-
        case lookupTmFunSig tt (objOwnerMode currentSort') f of
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

inferExpectedTmSort :: TypeTheory -> [Obj] -> Subst -> TermDiagram -> TermDiagram -> Either Text Obj
inferExpectedTmSort tt tmCtx subst lhs rhs =
  case inferTmSortFromTerm tt tmCtx subst lhs of
    Right ty -> Right ty
    Left _ -> inferTmSortFromTerm tt tmCtx subst rhs

inferTmSortFromTerm :: TypeTheory -> [Obj] -> Subst -> TermDiagram -> Either Text Obj
inferTmSortFromTerm tt _ixCtx subst tm =
  inferTmSortFromDiagram tt subst tm

inferTmSortFromDiagram :: TypeTheory -> Subst -> TermDiagram -> Either Text Obj
inferTmSortFromDiagram tt subst tm =
  case dOut (unTerm tm) of
    [pid] ->
      case diagramPortObj (unTerm tm) pid of
        Nothing -> Left "inferTmSortFromDiagram: missing output port type"
        Just ty -> applySubstObj tt subst ty
    _ -> Left "inferTmSortFromDiagram: term diagram must have exactly one output"

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

renderObj :: Obj -> Text
renderObj ty =
  "{owner="
    <> renderMode (objOwnerMode ty)
    <> ", code="
    <> renderCode (objCode ty)
    <> "}"
  where
    renderCode code =
      case code of
        CTMeta v -> renderObjVar v
        CTCon ref [] -> renderTypeRef ref
        CTCon ref args ->
          renderTypeRef ref <> "(" <> T.intercalate ", " (map renderArg args) <> ")"
        CTMod me inner -> renderModExpr me <> "(" <> renderCode inner <> ")"
        CTLift me inner -> "lift[" <> renderModExpr me <> "](" <> renderCode inner <> ")"

    renderArg arg =
      case arg of
        CAObj innerTy -> renderObj innerTy
        CATm _ -> "<tm>"

renderObjVar :: TmVar -> Text
renderObjVar v =
  tmvName v
    <> "@"
    <> renderMode
      ( case tmvOwnerMode v of
          Just owner -> owner
          Nothing -> objOwnerMode (tmvSort v)
      )

renderTypeRef :: ObjRef -> Text
renderTypeRef ref =
  renderMode (orMode ref) <> "." <> renderTypeName (orName ref)

renderTypeName :: ObjName -> Text
renderTypeName (ObjName n) = n

renderMode :: ModeName -> Text
renderMode (ModeName n) = n

renderModExpr :: ModExpr -> Text
renderModExpr me =
  case reverse (mePath me) of
    [] -> "id@" <> renderMode (meSrc me)
    names -> T.intercalate "." (map renderModName names)

renderModName :: ModName -> Text
renderModName (ModName n) = n
