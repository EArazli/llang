{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.UnifyObj
  ( Subst
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
import Strat.Poly.ModeTheory (ModeName(..), ModName(..), ModExpr(..))
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
  ( normalizeObjDeepWithCtx
  , normalizeTermDiagram
  , termToDiagram
  )
import Strat.Poly.TermExpr
  ( TermExpr(..)
  , diagramToTermExpr
  , termExprToDiagram
  , boundGlobalsExpr
  )


newtype Subst = Subst
  { unSubst :: M.Map TmVar CodeArg
  }
  deriving (Eq, Ord, Show)

data PortHead
  = PHBound Int
  | PHFun GenName [PortId]
  | PHMeta TmVar

lookupMeta :: Subst -> TmVar -> Maybe CodeArg
lookupMeta subst v =
  M.lookup v (unSubst subst)

lookupTmMeta :: Subst -> TmVar -> Maybe TermDiagram
lookupTmMeta subst v =
  case lookupMeta subst v of
    Just (CATm tm) -> Just tm
    _ -> Nothing

lookupCodeMeta :: Subst -> TmVar -> Maybe Obj
lookupCodeMeta subst v =
  case lookupMeta subst v of
    Just (CAObj t) -> Just t
    _ -> Nothing

tmBindings :: Subst -> [(TmVar, TermDiagram)]
tmBindings subst =
  [ (v, tm)
  | (v, CATm tm) <- M.toList (unSubst subst)
  ]

codeBindings :: Subst -> [(TmVar, Obj)]
codeBindings subst =
  [ (v, t)
  | (v, CAObj t) <- M.toList (unSubst subst)
  ]

allBindings :: Subst -> [(TmVar, CodeArg)]
allBindings = M.toList . unSubst

insertMeta :: TmVar -> CodeArg -> Subst -> Either Text Subst
insertMeta v arg subst =
  case lookupMeta subst v of
    Just old | category old /= category arg ->
      Left
        ( "insertMeta: category conflict for metavariable "
            <> tmvName v
            <> " (existing "
            <> category old
            <> ", new "
            <> category arg
            <> ")"
        )
    _ ->
      Right subst { unSubst = M.insert v arg (unSubst subst) }
  where
    category :: CodeArg -> Text
    category binding =
      case binding of
        CAObj _ -> "type-level"
        CATm _ -> "term-level"

insertCodeMeta :: TmVar -> Obj -> Subst -> Either Text Subst
insertCodeMeta v t subst =
  insertMeta v (CAObj t) subst

insertTmMeta :: TmVar -> TermDiagram -> Subst -> Either Text Subst
insertTmMeta v tm subst =
  insertMeta v (CATm tm) subst

mkSubst :: [(TmVar, CodeArg)] -> Either Text Subst
mkSubst bindings =
  foldM
    (\subst (v, arg) -> insertMeta v arg subst)
    emptySubst
    bindings

emptySubst :: Subst
emptySubst = Subst M.empty

unifyObj :: TypeTheory -> Obj -> Obj -> Either Text Subst
unifyObj tt t1 t2 =
  let flex = S.union (freeVarsObj t1) (freeVarsObj t2)
   in unifyObjFlex tt [] flex emptySubst t1 t2

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
      do
        code' <- expandCode (objOwnerMode ty) (objCode ty)
        Right ty { objCode = code' }

    expandArg arg =
      case arg of
        CAObj ty -> CAObj <$> expandModSpine ty
        CATm tm -> Right (CATm tm)

    expandCode ownerMode code =
      case code of
        CTMeta _ -> Right code
        CTCon ref args -> do
          let codeMode = modeClassifierMode (ttModes tt) ownerMode
          if orMode ref == codeMode || isOpaqueMetaSort ref
            then Right ()
            else Left "unifyObjFlex: constructor mode does not match current code mode"
          args' <- mapM expandArg args
          Right (CTCon ref args')
        CTLift me innerCode -> do
          let codeMode = modeClassifierMode (ttModes tt) ownerMode
          if meTgt me == codeMode
            then Right ()
            else Left "unifyObjFlex: modality target does not match current code mode"
          inner' <- expandCodeInMode (meSrc me) innerCode
          normalizeCodeTerm (ttModes tt) (CTLift me inner')

    expandCodeInMode codeMode code =
      case code of
        CTMeta _ -> Right code
        CTCon ref args -> do
          if orMode ref == codeMode || isOpaqueMetaSort ref
            then Right ()
            else Left "unifyObjFlex: constructor mode does not match current code mode"
          args' <- mapM expandArg args
          Right (CTCon ref args')
        CTLift me innerCode -> do
          if meTgt me == codeMode
            then Right ()
            else Left "unifyObjFlex: modality target does not match current code mode"
          inner' <- expandCodeInMode (meSrc me) innerCode
          normalizeCodeTerm (ttModes tt) (CTLift me inner')

    unifyWith s a b =
      if objOwnerMode a /= objOwnerMode b
        then Left ("unifyObjFlex: owner-mode mismatch " <> renderObj a <> " with " <> renderObj b)
        else do
          let ownerMode = objOwnerMode a
          let codeMode = modeClassifierMode (ttModes tt) ownerMode
          unifyCode s codeMode ownerMode (objCode a) (objCode b)

    unifyCode s codeMode ownerMode codeA codeB =
      case (codeA, codeB) of
        (CTMeta v, CTMeta w) -> unifyTyVar s codeMode v (CTMeta w)
        (CTMeta v, t) -> unifyTyVar s codeMode v t
        (t, CTMeta v) -> unifyTyVar s codeMode v t
        (CTCon refA argsA, CTCon refB argsB)
          | refA == refB && length argsA == length argsB -> do
              if orMode refA == codeMode || isOpaqueMetaSort refA
                then Right ()
                else Left "unifyObjFlex: constructor mode does not match current code mode"
              case M.lookup (orName refA) sigTable of
                Just params
                  | length params == length argsA ->
                      foldl stepBySig (Right s) (zip params (zip argsA argsB))
                _ ->
                  foldl step (Right s) (zip argsA argsB)
          | otherwise ->
              Left ("unifyObjFlex: cannot unify " <> renderObj (mkObj ownerMode codeA) <> " with " <> renderObj (mkObj ownerMode codeB))
        (CTLift me1 innerA, CTLift me2 innerB)
          | me1 == me2 && meTgt me1 == codeMode ->
              unifyCode s (meSrc me1) ownerMode innerA innerB
          | otherwise ->
              Left ("unifyObjFlex: cannot unify " <> renderObj (mkObj ownerMode codeA) <> " with " <> renderObj (mkObj ownerMode codeB))
        _ ->
          Left ("unifyObjFlex: cannot unify " <> renderObj (mkObj ownerMode codeA) <> " with " <> renderObj (mkObj ownerMode codeB))
      where
        sigTable = M.findWithDefault M.empty codeMode (ttCtorSigs tt)

    isOpaqueMetaSort ref =
      case orName ref of
        ObjName "__obj_meta_sort" -> True
        _ -> False

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

    unifyTyVar s codeMode v tCode
      | v `S.member` flex = bindTyVar s codeMode v tCode
      | otherwise =
          case tCode of
            CTMeta v' | v == v' -> Right s
            CTMeta v' | v' `S.member` flex -> bindTyVar s codeMode v' (CTMeta v)
            _ -> Left ("unifyObjFlex: rigid variable mismatch " <> renderObjVar v <> " with " <> renderObj (mkObj codeMode tCode))

    bindTyVar s codeMode v tCode = do
      tmCtx' <- applySubstCtx tt s tmCtx
      let ownerV = tmVarOwner v
      let scopeMode = modeClassifierMode (ttModes tt) ownerV
      if scopeMode /= codeMode
        then Left "unifyObjFlex: code metavariable kind mismatch"
        else Right ()
      t' <- applySubstObj tt s Obj { objOwnerMode = ownerV, objCode = tCode }
      if ownerV /= objOwnerMode t'
        then Left ("unifyObjFlex: mode mismatch " <> renderObjVar v <> " with " <> renderObj t')
        else if t' == objVarObj v
          then Right s
        else if occursVar v t'
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
                    then do
                      singletonSubst <- mkSubst [(v, CAObj t')]
                      composeSubst tt singletonSubst s
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
        (TMMeta v args, TMMeta w args') -> do
          ensureTmTermSort s currentSort (TMMeta v args)
          ensureTmTermSort s currentSort (TMMeta w args')
          if sameTmVarId v w
            then
              if args == args'
                then Right s
                else Left "unifyTm: rigid term variable mismatch"
            else tryMetaMeta s currentSort v args w args'
        (TMMeta v args, t) -> do
          ensureTmTermSort s currentSort (TMMeta v args)
          ensureTmTermSort s currentSort t
          if v `S.member` tmFlex
            then bindTmVarAtSpine s currentSort v args t
            else Left "unifyTm: rigid term variable mismatch"
        (t, TMMeta v args) -> do
          ensureTmTermSort s currentSort t
          ensureTmTermSort s currentSort (TMMeta v args)
          if v `S.member` tmFlex
            then bindTmVarAtSpine s currentSort v args t
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

    tryMetaMeta s currentSort v args w args' =
      case bindLeft of
        Right s' -> Right s'
        Left leftErr ->
          if w `S.member` tmFlex
            then
              case bindTmVarAtSpine s currentSort w args' (TMMeta v args) of
                Right s' -> Right s'
                Left _ -> Left leftErr
            else Left leftErr
      where
        bindLeft =
          if v `S.member` tmFlex
            then bindTmVarAtSpine s currentSort v args (TMMeta w args')
            else Left "unifyTm: rigid term variable mismatch"

    bindTmVarAtSpine s currentSort v spine t = do
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
          tAbs <- abstractOverSpineToFormals tmCtx' v spine t'
          tDiag <- termExprToDiagram tt tmCtx' sortV tAbs
          singletonSubst <- mkSubst [(v, CATm tDiag)]
          composeSubst tt singletonSubst s

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
        TMMeta v args -> do
          checkTmVarSort s currentSort v
          if length args == tmvScope v
            then Right ()
            else
              Left
                ( "unifyTm: metavariable spine arity mismatch for "
                    <> tmvName v
                    <> " (expected "
                    <> T.pack (show (tmvScope v))
                    <> ", got "
                    <> T.pack (show (length args))
                    <> ")"
                )
          if all (\i -> i >= 0 && i < length tmCtx) args
            then Right ()
            else
              Left
                ( "unifyTm: metavariable spine index out of range for "
                    <> tmvName v
                )
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
            TMMeta v args -> do
              sort' <- applySubstObj tt s (tmvSort v)
              let v' = v { tmvSort = sort' }
              case lookupTmMeta s v' of
                Nothing -> Right (TMMeta v' args)
                Just tmSub ->
                  if v' `S.member` seen
                    then Right (TMMeta v' args)
                    else do
                      subExpr0 <- diagramToTermExpr tt ctx sort' tmSub
                      subExpr <- instantiateMetaBody ctx v' args subExpr0
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
            PGen fName attrs bargs
              | M.null attrs && null bargs -> Right (PHFun fName (eIns edge))
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
                    PGen fName attrs bargs
                      | M.null attrs && null bargs -> do
                          args <- mapM (go (S.insert pid0 seen)) (eIns edge)
                          Right (TMFun fName args)
                      | otherwise ->
                          Left "unifyTm: non-term generator payload in normalized term graph"
                    PTmMeta v -> do
                      metaArgs <- mapM boundaryGlobal (eIns edge)
                      Right (TMMeta v metaArgs)
                    _ ->
                      Left "unifyTm: non-term payload in normalized term graph"
        boundaryGlobal inp =
          case M.lookup inp inputs of
            Just i -> Right i
            Nothing -> Left "unifyTm: PTmMeta inputs must connect to boundary inputs"

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
  tmCtx <- inferObjTmCtx raw
  normalizeObjDeepWithCtx tt tmCtx raw
  where
    -- | Infer a term-context large enough to deep-normalize an object by
    -- | merging the term-contexts of all embedded term arguments.
    --
    -- This is the least upper bound of all embedded dTmCtx's under the prefix order
    -- (implemented by mergeTermCtx). If an Obj contains embedded terms whose contexts
    -- are incompatible (non-prefix-compatible), the Obj is ill-formed and we fail.
    inferObjTmCtx :: Obj -> Either Text [Obj]
    inferObjTmCtx o = do
      let ctxs = collectObjCtxs o
      foldM mergeTermCtx [] ctxs

    collectObjCtxs :: Obj -> [[Obj]]
    collectObjCtxs Obj { objCode = code } = collectCodeCtxs code

    collectCodeCtxs :: CodeTerm -> [[Obj]]
    collectCodeCtxs c =
      case c of
        CTMeta _ -> []
        CTLift _ inner -> collectCodeCtxs inner
        CTCon _ args -> concatMap collectArgCtxs args

    collectArgCtxs :: CodeArg -> [[Obj]]
    collectArgCtxs a =
      case a of
        CAObj inner -> collectObjCtxs inner
        CATm tm -> [dTmCtx (unTerm tm)]

    goTy seen expr =
      let ownerMode = objOwnerMode expr
          codeMode = modeClassifierMode (ttModes tt) ownerMode
       in do
            code' <- goCode seen ownerMode codeMode (objCode expr)
            Right expr { objCode = code' }

    goCode seen ownerMode codeMode code =
      case code of
        CTMeta v ->
          case lookupCodeMeta subst v of
            Nothing -> Right code
            Just t ->
              if v `S.member` seen
                then Right code
                else do
                  let tCodeMode = modeClassifierMode (ttModes tt) (objOwnerMode t)
                  if tCodeMode == codeMode
                    then goCode (S.insert v seen) (objOwnerMode t) codeMode (objCode t)
                    else Left "applySubstObj: code metavariable mode mismatch"
        CTCon ref args -> do
          if orMode ref == codeMode || isOpaqueMetaSort ref
            then Right ()
            else Left "applySubstObj: constructor mode does not match current code mode"
          let sigTableForCode = M.findWithDefault M.empty codeMode (ttCtorSigs tt)
          args' <-
            case M.lookup (orName ref) sigTableForCode of
              Just params ->
                if length params /= length args
                  then Left "applySubstObj: type constructor arity mismatch"
                  else mapM (goArgBySig seen) (zip params args)
              Nothing ->
                mapM (goArgNoSig seen) args
          Right (CTCon ref args')
        CTLift me innerCode -> do
          if meTgt me == codeMode
            then do
              inner' <- goCode seen ownerMode (meSrc me) innerCode
              Right (CTLift me inner')
            else Left "applySubstObj: lift target does not match current code mode"

    isOpaqueMetaSort ref =
      case orName ref of
        ObjName "__obj_meta_sort" -> True
        _ -> False

    goArgBySig seen (param, arg) =
      case (param, arg) of
        (TPS_Ty _, CAObj innerTy) ->
          CAObj <$> goTy seen innerTy
        (TPS_Tm sortTy, CATm tmArg) -> do
          sort' <- goTy seen sortTy
          CATm <$> applySubstTm tt subst sort' tmArg
        (TPS_Ty _, CATm _) ->
          Left "applySubstObj: expected type argument for constructor parameter"
        (TPS_Tm _, CAObj _) ->
          Left "applySubstObj: expected term argument for constructor parameter"

    goArgNoSig seen arg =
      case arg of
        CAObj innerTy -> CAObj <$> goTy seen innerTy
        CATm tmArg -> do
          sort <- inferTmSortFromDiagram tt subst tmArg
          CATm <$> applySubstTm tt subst sort tmArg

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
          pure (PTmMeta (v { tmvSort = sort' }))
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
  (tmCtxOut, expr') <- substituteTermExprMetas tt subst tmCtx' expectedSort' expr
  expectedSortOut <- normalizeObjDeepWithCtx tt tmCtxOut expectedSort0
  tm' <- termExprToDiagram tt tmCtxOut expectedSortOut expr'
  normalizeTermDiagram tt tmCtxOut expectedSortOut tm'

applySubstCtx :: TypeTheory -> Subst -> Context -> Either Text Context
applySubstCtx tt subst = mapM (applySubstObj tt subst)

normalizeSubst :: TypeTheory -> Subst -> Either Text Subst
normalizeSubst tt subst = do
  pairs <- mapM normBinding (allBindings subst)
  Right
    ( Subst
        ( M.fromList
            [ (v, binding)
            | (v, binding) <- pairs
            , not (isIdentity v binding)
            ]
        )
    )
  where
    normBinding (v, binding) =
      case binding of
        CAObj t -> do
          t' <- applySubstObj tt subst t
          pure (v, CAObj t')
        CATm t -> do
          sort' <- applySubstObj tt subst (tmvSort v)
          t' <- applySubstTm tt subst sort' t
          pure (v { tmvSort = sort' }, CATm t')

    isIdentity v binding =
      case binding of
        CAObj t -> t == OVar v
        CATm t -> isTmIdentity v t

composeSubst :: TypeTheory -> Subst -> Subst -> Either Text Subst
composeSubst tt s2 s1 = do
  appliedPairs <- mapM (substPair s2) (allBindings s1)
  let appliedMap = M.fromList appliedPairs
  ensureCategoryCompatible appliedMap (unSubst s2)
  normalizeSubst tt (Subst (M.union appliedMap (unSubst s2)))
  where
    substPair subst (v, binding) =
      case binding of
        CAObj t -> do
          t' <- applySubstObj tt subst t
          pure (v, CAObj t')
        CATm t -> do
          sort' <- applySubstObj tt subst (tmvSort v)
          t' <- applySubstTm tt subst sort' t
          pure (v { tmvSort = sort' }, CATm t')

    ensureCategoryCompatible left right =
      mapM_ checkPair (M.toList (M.intersectionWith (,) left right))

    checkPair (v, (leftBinding, rightBinding))
      | sameCategory leftBinding rightBinding = Right ()
      | otherwise =
          Left
            ( "composeSubst: category conflict for metavariable "
                <> tmvName v
            )

    sameCategory a b =
      case (a, b) of
        (CAObj _, CAObj _) -> True
        (CATm _, CATm _) -> True
        _ -> False

substituteTermExprMetas
  :: TypeTheory
  -> Subst
  -> [Obj]
  -> Obj
  -> TermExpr
  -> Either Text ([Obj], TermExpr)
substituteTermExprMetas tt subst =
  go S.empty
  where
    go seen curCtx currentSort expr =
      case expr of
        TMMeta v args -> do
          sort' <- applySubstObj tt subst (tmvSort v)
          let v' = v { tmvSort = sort' }
          case lookupTmMeta subst v' of
            Nothing -> Right (curCtx, TMMeta v' args)
            Just tmSub ->
              if v' `S.member` seen
                then Right (curCtx, TMMeta v' args)
                else do
                  subCtx0 <- applySubstCtx tt subst (dTmCtx (unTerm tmSub))
                  sortSub <- normalizeObjDeepWithCtx tt subCtx0 sort'
                  subExpr0 <- diagramToTermExpr tt subCtx0 sortSub tmSub
                  merged0 <- mergeTermCtx curCtx subCtx0
                  subExpr <- instantiateMetaBody merged0 v' args subExpr0
                  (subCtx, subExpr') <- go (S.insert v' seen) merged0 currentSort subExpr
                  Right (subCtx, subExpr')
        TMBound _ -> Right (curCtx, expr)
        TMFun f args -> do
          sig <- requireSig curCtx currentSort f (length args)
          (ctxOut, argsRev) <-
            foldM
              (\(ctxAcc, acc) (argSort, argTm) -> do
                argSort' <- normalizeObjDeepWithCtx tt ctxAcc =<< applySubstObj tt subst argSort
                (ctxArg, argExpr) <- go seen ctxAcc argSort' argTm
                ctxNext <- mergeTermCtx ctxAcc ctxArg
                Right (ctxNext, argExpr : acc))
              (curCtx, [])
              (zip (tfsArgs sig) args)
          Right (ctxOut, TMFun f (reverse argsRev))

    requireSig curCtx currentSort f arity = do
      currentSort' <- normalizeObjDeepWithCtx tt curCtx =<< applySubstObj tt subst currentSort
      sig <-
        case lookupTmFunSig tt (objOwnerMode currentSort') f of
          Nothing -> Left "applySubstTm: unknown term function"
          Just s -> Right s
      if length (tfsArgs sig) == arity
        then Right sig
        else Left "applySubstTm: term function arity mismatch"

mergeTermCtx :: [Obj] -> [Obj] -> Either Text [Obj]
mergeTermCtx left right =
  let maxLen = max (length left) (length right)
  in mapM pick [0 :: Int .. maxLen - 1]
  where
    pick i =
      case (nth left i, nth right i) of
        (Just a, Just b) ->
          if a == b
            then Right a
            else Left "applySubstTm: incompatible term contexts during substitution"
        (Just a, Nothing) -> Right a
        (Nothing, Just b) -> Right b
        (Nothing, Nothing) -> Left "applySubstTm: internal context merge failure"

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

renameTermGlobalsPartial :: M.Map Int Int -> TermExpr -> TermExpr
renameTermGlobalsPartial ren tm =
  case tm of
    TMBound i -> TMBound (M.findWithDefault i i ren)
    TMMeta v args -> TMMeta v (map (\i -> M.findWithDefault i i ren) args)
    TMFun f args -> TMFun f (map (renameTermGlobalsPartial ren) args)

instantiateMetaBody
  :: [Obj]
  -> TmVar
  -> [Int]
  -> TermExpr
  -> Either Text TermExpr
instantiateMetaBody tmCtx v spine body = do
  let formal = defaultMetaArgs tmCtx v
      scope = tmvScope v
  if length formal == scope
    then Right ()
    else Left "instantiateMetaBody: default-meta spine arity does not match scope"
  if length spine == scope
    then Right ()
    else
      Left
        ( "instantiateMetaBody: occurrence spine arity mismatch for "
            <> tmvName v
            <> " (expected "
            <> T.pack (show scope)
            <> ", got "
            <> T.pack (show (length spine))
            <> ")"
        )
  let ren = M.fromList (zip formal spine)
  pure (renameTermGlobalsPartial ren body)

abstractOverSpineToFormals
  :: [Obj]
  -> TmVar
  -> [Int]
  -> TermExpr
  -> Either Text TermExpr
abstractOverSpineToFormals tmCtx v spine rhs = do
  let scope = tmvScope v
      formal = defaultMetaArgs tmCtx v
      spineSet = S.fromList spine
      boundSet = boundGlobalsExpr rhs
  if length formal == scope
    then Right ()
    else Left "abstractOverSpineToFormals: default-meta spine arity does not match scope"
  if length spine == scope
    then Right ()
    else
      Left
        ( "unifyTm: metavariable spine arity mismatch for "
            <> tmvName v
            <> " (expected "
            <> T.pack (show scope)
            <> ", got "
            <> T.pack (show (length spine))
            <> ")"
        )
  if S.size spineSet == length spine
    then Right ()
    else
      Left
        ( "unifyTm: metavariable solving spine must be injective for "
            <> tmvName v
        )
  if S.isSubsetOf boundSet spineSet
    then Right ()
    else Left "unifyTm: escape from bound term-variable scope"
  let ren = M.fromList (zip spine formal)
  pure (renameTermGlobalsPartial ren rhs)

occursTmVarExpr :: TmVar -> TermExpr -> Bool
occursTmVarExpr v tm =
  case tm of
    TMMeta v' _ -> v == v'
    TMBound _ -> False
    TMFun _ args -> any (occursTmVarExpr v) args

isTmIdentity :: TmVar -> TermDiagram -> Bool
isTmIdentity v tm =
  case IM.elems (dEdges (unTerm tm)) of
    [edge] ->
      case (ePayload edge, eIns edge, eOuts edge, dIn (unTerm tm), dOut (unTerm tm)) of
        (PTmMeta w, [], [outPid], [], [outBoundary]) ->
          outPid == outBoundary && v == w
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
        CTLift me inner -> "lift[" <> renderModExpr me <> "](" <> renderCode inner <> ")"

    renderArg arg =
      case arg of
        CAObj innerTy -> renderObj innerTy
        CATm _ -> "<tm>"

renderObjVar :: TmVar -> Text
renderObjVar v =
  tmvName v
    <> "@"
    <> renderMode (tmVarOwner v)

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
