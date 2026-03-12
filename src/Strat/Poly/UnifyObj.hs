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
  , unifyCodeArgFlex
  , unifyCodeArgsFlex
  , unifyGenArgsFlex
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
import Strat.Poly.Literal (Literal, literalKind)
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
  , TmHeadSig(..)
  , literalKindForObj
  , lookupTmHeadSig
  )
import Strat.Poly.Tele (GenParam(..))
import Strat.Poly.Traversal (traverseDiagram)
import Strat.Poly.DefEq
  ( normalizeObjDeepWithCtx
  , normalizeTermDiagram
  , termToDiagram
  )
import Strat.Poly.TermExpr
  ( TermExpr(..)
  , ResolvedHeadArgs(..)
  , applyHeadSubstObj
  , bindHeadSubst
  , boundGlobalsExpr
  , diagramToTermExpr
  , instantiateMetaBody
  , resolveHeadArgsExpr
  , resolvedHeadFlatArgs
  , structuralConvEnv
  , termExprToDiagram
  )
import Strat.Poly.Term.AST (TermHeadArg(..))


newtype Subst = Subst
  { unSubst :: M.Map TmVar CodeArg
  }
  deriving (Eq, Ord, Show)

data PortHead
  = PHBound Int
  | PHGen GenName [CodeArg] [PortId]
  | PHMeta TmVar
  | PHLit Literal

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

unifyCodeArgFlex
  :: TypeTheory
  -> [Obj]
  -> S.Set TmVar
  -> Subst
  -> CodeArg
  -> CodeArg
  -> Either Text Subst
unifyCodeArgFlex tt tmCtx flex subst argA argB =
  case (argA, argB) of
    (CAObj tyA, CAObj tyB) ->
      unifyObjFlex tt tmCtx flex subst tyA tyB
    (CATm tmA, CATm tmB) -> do
      sort <- inferExpectedTmSort tt tmCtx subst tmA tmB
      unifyTm tt tmCtx flex subst sort tmA tmB
    _ ->
      Left "unifyCodeArgFlex: mixed type/term arguments cannot unify"

unifyCodeArgsFlex
  :: TypeTheory
  -> [Obj]
  -> S.Set TmVar
  -> Subst
  -> [CodeArg]
  -> [CodeArg]
  -> Either Text Subst
unifyCodeArgsFlex tt tmCtx flex subst argsA argsB
  | length argsA /= length argsB =
      Left "unifyCodeArgsFlex: arity mismatch"
  | otherwise =
      foldM
        (\s (argA, argB) -> unifyCodeArgFlex tt tmCtx flex s argA argB)
        subst
        (zip argsA argsB)

unifyGenArgsFlex
  :: TypeTheory
  -> [Obj]
  -> S.Set TmVar
  -> Subst
  -> [GenParam]
  -> [CodeArg]
  -> [CodeArg]
  -> Either Text Subst
unifyGenArgsFlex tt tmCtx flex subst params argsA argsB
  | length params /= length argsA || length params /= length argsB =
      Left "unifyGenArgsFlex: arity mismatch"
  | otherwise =
      foldM step subst (zip3 params argsA argsB)
  where
    step s (param, argA, argB) =
      case (param, argA, argB) of
        (GP_Ty _, CAObj tyA, CAObj tyB) ->
          unifyObjFlex tt tmCtx flex s tyA tyB
        (GP_Tm v, CATm tmA, CATm tmB) -> do
          expectedSort <- applySubstObj tt s (tmvSort v)
          unifyTm tt tmCtx flex s expectedSort tmA tmB
        (GP_Ty _, CATm _, _) ->
          Left "unifyGenArgsFlex: expected type argument"
        (GP_Ty _, _, CATm _) ->
          Left "unifyGenArgsFlex: expected type argument"
        (GP_Tm _, CAObj _, _) ->
          Left "unifyGenArgsFlex: expected term argument"
        (GP_Tm _, _, CAObj _) ->
          Left "unifyGenArgsFlex: expected term argument"

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
            (PHGen f lStored lIns, PHGen g rStored rIns)
              | f == g && length lIns == length rIns -> do
                  sig <- requireFunSigArity s currentSort f (length lStored + length lIns)
                  s1 <- unifyGenArgsFlex tt tmCtx tmFlex s (thsParams sig) lStored rStored
                  foldM
                    (\s1 (argSort, lArg, rArg) -> do
                      argSort0 <- applySubstObj tt s1 argSort
                      tmCtx1 <- applySubstCtx tt s1 tmCtx
                      argSort' <- normalizeObjDeepWithCtx tt tmCtx1 argSort0
                      unifyTmGraph s1 seen' argSort' lhsDiag lhsInputs lArg rhsDiag rhsInputs rArg
                    )
                    s1
                    (zip3 (thsInputs sig) lIns rIns)
              | otherwise ->
                  Left "unifyTm: term head mismatch"
            (PHLit l1, PHLit l2)
              | l1 == l2 -> Right s
              | otherwise -> Left "unifyTm: literal mismatch"
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
        (TMGen f xs, TMGen g ys)
          | f == g && length xs == length ys -> do
              resolvedL <- canonicalizeHeadAtSubst s currentSort f xs
              resolvedR <- canonicalizeHeadAtSubst s currentSort g ys
              let sig = rhaSig resolvedL
              sParam <- unifyGenArgsFlex tt tmCtx tmFlex s (thsParams sig) (rhaStoredCodeArgs resolvedL) (rhaStoredCodeArgs resolvedR)
              foldM step sParam (zip3 (thsInputs sig) (map snd (rhaInputs resolvedL)) (map snd (rhaInputs resolvedR)))
          | otherwise -> Left "unifyTm: term head mismatch"
        (TMLit l1, TMLit l2) -> do
          ensureTmTermSort s currentSort (TMLit l1)
          ensureTmTermSort s currentSort (TMLit l2)
          if l1 == l2
            then Right s
            else Left "unifyTm: literal mismatch"
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
        step s1 (argSort, xTm, yTm) = do
          tmCtx1 <- applySubstCtx tt s1 tmCtx
          argSort0 <- applySubstObj tt s1 argSort
          argSort' <- normalizeObjDeepWithCtx tt tmCtx1 argSort0
          x' <- applySubstExprInCtx tmCtx1 s1 argSort' xTm
          y' <- applySubstExprInCtx tmCtx1 s1 argSort' yTm
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
        TMGen f args -> do
          resolved <- canonicalizeHeadAtSubst s currentSort f args
          mapM_ (uncurry (ensureTmTermSort s)) (rhaInputs resolved)
        TMLit lit -> do
          currentSort' <- normalizeInCtx s currentSort
          case literalKindForObj tt currentSort' of
            Just kind
              | kind == literalKind lit -> Right ()
              | otherwise -> Left "unifyTm: literal kind does not match expected sort"
            Nothing -> Left "unifyTm: expected sort does not admit literals"

    requireFunSigArity s currentSort f arity = do
      currentSort0 <- applySubstObj tt s currentSort
      currentSort' <- normalizeInCtx s currentSort0
      sig <-
        case lookupTmHeadSig tt (objOwnerMode currentSort') f of
          Nothing -> Left "unifyTm: unknown term head"
          Just sig' -> Right sig'
      if length (thsParams sig) + length (thsInputs sig) /= arity
        then Left "unifyTm: term head arity mismatch"
        else Right ()
      resSort0 <- applySubstObj tt s (thsRes sig)
      resSort <- normalizeInCtx s resSort0
      if resSort == currentSort'
        then Right sig
        else Left "unifyTm: term head result sort mismatch"

    canonicalizeHeadAtSubst s currentSort f args = do
      tmCtx1 <- applySubstCtx tt s tmCtx
      currentSort' <- normalizeObjDeepWithCtx tt tmCtx1 =<< applySubstObj tt s currentSort
      expr' <- applySubstExprInCtx tmCtx1 s currentSort' (TMGen f args)
      case expr' of
        TMGen f' args'
          | f' == f ->
              resolveHeadArgsExpr tt (structuralConvEnv tt) tmCtx1 M.empty currentSort' f args'
          | otherwise ->
              Left "unifyTm: substituted term head changed unexpectedly"
        _ ->
          Left "unifyTm: substituted term head did not remain a head application"

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
            TMGen f args -> do
              sig <- requireFunSigArity s currentSort f (length args)
              let (paramArgs, inputArgs) = splitAt (length (thsParams sig)) args
              (paramArgsRev, headSubst) <-
                foldM
                  (applyParamHeadArg seen)
                  ([], M.empty)
                  (zip (thsParams sig) paramArgs)
              inputArgsRev <-
                foldM
                  (applyInputHeadArg seen headSubst)
                  []
                  (zip (thsInputs sig) inputArgs)
              canonicalizeHead currentSort f (reverse paramArgsRev <> reverse inputArgsRev)
            TMLit _ -> Right tm

        applyParamHeadArg seen (acc, headSubst) (param, arg) =
          case (param, arg) of
            (GP_Ty v, THAObj obj) -> do
              obj' <- normalizeObjDeepWithCtx tt ctx =<< applySubstObj tt s obj
              headSubst' <- bindHeadSubst v (CAObj obj') headSubst
              Right (THAObj obj' : acc, headSubst')
            (GP_Ty _, THATm _) -> Left "applySubstTm: expected object-valued parameter argument"
            (GP_Tm v, THATm tmArg) -> do
              expectedSort0 <- applyHeadSubstObj tt (structuralConvEnv tt) ctx headSubst (tmvSort v)
              expectedSort <- normalizeObjDeepWithCtx tt ctx =<< applySubstObj tt s expectedSort0
              tmArg' <- go seen expectedSort tmArg
              tmDiag <- termExprToDiagram tt ctx expectedSort tmArg'
              headSubst' <- bindHeadSubst v (CATm tmDiag) headSubst
              Right (THATm tmArg' : acc, headSubst')
            (GP_Tm _, THAObj _) -> Left "applySubstTm: expected term-valued parameter argument"

        applyInputHeadArg seen headSubst acc (argSort, arg) =
          case arg of
            THATm tmArg -> do
              expectedSort0 <- applyHeadSubstObj tt (structuralConvEnv tt) ctx headSubst argSort
              expectedSort <- normalizeObjDeepWithCtx tt ctx =<< applySubstObj tt s expectedSort0
              tmArg' <- go seen expectedSort tmArg
              Right (THATm tmArg' : acc)
            THAObj _ -> Left "applySubstTm: expected term input argument"

        canonicalizeHead currentSort f flatArgs = do
          resolved <- resolveHeadArgsExpr tt (structuralConvEnv tt) ctx M.empty currentSort f flatArgs
          Right (TMGen f (resolvedHeadFlatArgs resolved))

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
            PGen fName args bargs
              | null bargs -> Right (PHGen fName args (eIns edge))
              | otherwise -> Left "unifyTm: non-term generator payload in normalized term graph"
            PTmMeta v -> Right (PHMeta v)
            PTmLit lit -> Right (PHLit lit)
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
                    PGen fName args bargs
                      | null bargs -> do
                          sig <-
                            case lookupTmHeadSig tt (dMode diag) fName of
                              Just sig'
                                | length (thsParams sig') + length (thsInputs sig') == length args + length (eIns edge) ->
                                    Right sig'
                              Just _ -> Left "unifyTm: term head arity mismatch in normalized term graph"
                              Nothing -> Left "unifyTm: unknown term head in normalized term graph"
                          storedArgs <- mapM (uncurry rebuildStoredArg) (zip (thsParams sig) args)
                          inputArgs <- mapM (fmap THATm . go (S.insert pid0 seen)) (eIns edge)
                          Right (TMGen fName (storedArgs <> inputArgs))
                      | otherwise ->
                          Left "unifyTm: non-term generator payload in normalized term graph"
                    PTmMeta v -> do
                      metaArgs <- mapM boundaryGlobal (eIns edge)
                      Right (TMMeta v metaArgs)
                    PTmLit lit ->
                      Right (TMLit lit)
                    _ ->
                      Left "unifyTm: non-term payload in normalized term graph"
        boundaryGlobal inp =
          case M.lookup inp inputs of
            Just i -> Right i
            Nothing -> Left "unifyTm: PTmMeta inputs must connect to boundary inputs"
        rebuildStoredArg param arg =
          case (param, arg) of
            (GP_Ty _, CAObj obj) -> Right (THAObj obj)
            (GP_Ty _, CATm _) -> Left "unifyTm: expected object-valued stored arg"
            (GP_Tm v, CATm tmArg) -> THATm <$> diagramToTermExpr tt tmCtx (tmvSort v) tmArg
            (GP_Tm _, CAObj _) -> Left "unifyTm: expected term-valued stored arg"

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
  traverseDiagram onDiag onPayload onCodeArg pure
  where
    onDiag d = do
      dPortObj' <- IM.traverseWithKey (\_ ty -> applySubstObj tt subst ty) (dPortObj d)
      dTmCtx' <- mapM (applySubstObj tt subst) (dTmCtx d)
      pure d { dTmCtx = dTmCtx', dPortObj = dPortObj' }
    onPayload payload =
      case payload of
        PGen g args bargs ->
          pure (PGen g args bargs)
        PTmMeta v -> do
          sort' <- applySubstObj tt subst (tmvSort v)
          pure (PTmMeta (v { tmvSort = sort' }))
        PTmLit lit ->
          pure (PTmLit lit)
        _ -> pure payload

    onCodeArg arg =
      case arg of
        CAObj obj -> CAObj <$> applySubstObj tt subst obj
        CATm tmArg -> do
          sort <- inferTmSortFromDiagram tt subst tmArg
          CATm <$> applySubstTm tt subst sort tmArg

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
        TMGen f args -> do
          sig <- requireSig curCtx currentSort f (length args)
          let (paramArgs, inputArgs) = splitAt (length (thsParams sig)) args
          (ctxAfterParams, paramArgsRev, headSubst) <-
            foldM
              (stepParam seen)
              (curCtx, [], M.empty)
              (zip (thsParams sig) paramArgs)
          (ctxOut, inputArgsRev) <-
            foldM
              (stepInput seen headSubst)
              (ctxAfterParams, [])
              (zip (thsInputs sig) inputArgs)
          currentSort' <- normalizeObjDeepWithCtx tt ctxOut =<< applySubstObj tt subst currentSort
          let flatArgs = reverse paramArgsRev <> reverse inputArgsRev
          resolved <- resolveHeadArgsExpr tt (structuralConvEnv tt) ctxOut M.empty currentSort' f flatArgs
          Right (ctxOut, TMGen f (resolvedHeadFlatArgs resolved))
        TMLit _ -> Right (curCtx, expr)

    stepParam seen (ctxAcc, acc, headSubst) (param, arg) =
      case (param, arg) of
        (GP_Ty v, THAObj obj) -> do
          obj' <- normalizeObjDeepWithCtx tt ctxAcc =<< applySubstObj tt subst obj
          headSubst' <- bindHeadSubst v (CAObj obj') headSubst
          Right (ctxAcc, THAObj obj' : acc, headSubst')
        (GP_Ty _, THATm _) -> Left "applySubstTm: expected object-valued parameter argument"
        (GP_Tm v, THATm tm0) -> do
          sort0 <- applyHeadSubstObj tt (structuralConvEnv tt) ctxAcc headSubst (tmvSort v)
          sort' <- normalizeObjDeepWithCtx tt ctxAcc =<< applySubstObj tt subst sort0
          (ctxArg, tm1) <- go seen ctxAcc sort' tm0
          ctxNext <- mergeTermCtx ctxAcc ctxArg
          tmDiag <- termExprToDiagram tt ctxNext sort' tm1
          headSubst' <- bindHeadSubst v (CATm tmDiag) headSubst
          Right (ctxNext, THATm tm1 : acc, headSubst')
        (GP_Tm _, THAObj _) -> Left "applySubstTm: expected term-valued parameter argument"

    stepInput seen headSubst (ctxAcc, acc) (argSort, arg) = do
      sort0 <- applyHeadSubstObj tt (structuralConvEnv tt) ctxAcc headSubst argSort
      sort' <- normalizeObjDeepWithCtx tt ctxAcc =<< applySubstObj tt subst sort0
      tmExpr <-
        case arg of
          THATm tm0 -> Right tm0
          THAObj _ -> Left "applySubstTm: expected term input argument"
      (ctxArg, argExpr) <- go seen ctxAcc sort' tmExpr
      ctxNext <- mergeTermCtx ctxAcc ctxArg
      Right (ctxNext, THATm argExpr : acc)

    requireSig curCtx currentSort f arity = do
      currentSort' <- normalizeObjDeepWithCtx tt curCtx =<< applySubstObj tt subst currentSort
      sig <-
        case lookupTmHeadSig tt (objOwnerMode currentSort') f of
          Nothing -> Left "applySubstTm: unknown term head"
          Just s -> Right s
      if length (thsParams sig) + length (thsInputs sig) == arity
        then Right sig
        else Left "applySubstTm: term head arity mismatch"

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
    TMGen f args -> TMGen f (map renameHeadArg args)
    TMLit lit -> TMLit lit
  where
    renameHeadArg arg =
      case arg of
        THAObj obj -> THAObj obj
        THATm tm0 -> THATm (renameTermGlobalsPartial ren tm0)

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
    TMGen _ args -> any occursHeadArg args
    TMLit _ -> False
  where
    occursHeadArg arg =
      case arg of
        THAObj _ -> False
        THATm tm0 -> occursTmVarExpr v tm0

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
