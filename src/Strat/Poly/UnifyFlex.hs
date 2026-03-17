{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
module Strat.Poly.UnifyFlex
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
  , substIsEmpty
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.IntMap.Strict as IM
import Data.Monoid (Any(..))
import Control.Monad (foldM)
import Strat.Poly.Alpha (freshenTmHeadSigAgainst)
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
  , canonDiagramRaw
  , diagramPortObj
  , unPortId
  , unEdgeId
  )
import Strat.Poly.TypeTheory
  ( TypeTheory(..)
  , TmHeadSig(..)
  , literalKindForObj
  , lookupTmHeadSig
  )
import Strat.Poly.Tele (CtorSig(..), GenParam(..))
import Strat.Poly.Term.DefEqCore
  ( normalizeObjDeepWithCtx
  , normalizeTermDiagram
  , termToDiagram
  )
import Strat.Poly.Term.SubstRuntime
  ( applySubstCtx
  , applySubstDiagram
  , applySubstObj
  , applySubstTm
  , applySubstTmInCtx
  , composeSubst
  )
import Strat.Poly.Subst
  ( Subst
  , bindHeadSubst
  , codeBindings
  , emptySubst
  , insertCodeMeta
  , insertTmMeta
  , lookupCodeMeta
  , lookupTmMeta
  , mkSubst
  , substDomain
  , substIsEmpty
  , tmBindings
  )
import Strat.Poly.TermExpr
  ( TermExpr(..)
  , ResolvedHeadArgs(..)
  , applyHeadSubstObj
  , diagramToTermExpr
  , freeTmVarsExpr
  , pattern TMGen
  , resolveHeadArgsExpr
  , structuralConvEnv
  , termExprToDiagram
  )
import Strat.Poly.Term.AST (TermBinderArg(..), TermHeadArg(..))
import Strat.Poly.Term.GraphRead (TermPortReader(..), readTermPort)
import Strat.Poly.Term.Scope (hostBoundGlobalsExpr, renameTermGlobalsPartial)
import Strat.Poly.Traversal (foldDiagram)

data PortHead
  = PHBound Int
  | PHGen GenName [CodeArg] [PortId]
  | PHMeta TmVar
  | PHLit Literal

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
                Just sig
                  | length (csParams sig) == length argsA ->
                      fst <$> foldM stepBySig (s, M.empty) (zip (csParams sig) (zip argsA argsB))
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

    stepBySig (s, headSubst) (param, (argA, argB)) =
      case (param, argA, argB) of
        (GP_Ty v, CAObj tyA, CAObj tyB) -> do
          s' <- unifyObjFlex tt tmCtx flex s tyA tyB
          tyA' <- applySubstObj tt s' tyA
          headSubst' <- bindHeadSubst v (CAObj tyA') headSubst
          Right (s', headSubst')
        (GP_Tm v, CATm tmA, CATm tmB) -> do
          expectedSort <- applyHeadSubstObj tt (structuralConvEnv tt) tmCtx headSubst (tmvSort v)
          s' <- unifyTm tt tmCtx flex s expectedSort tmA tmB
          tmA' <- applySubstTm tt s' expectedSort tmA
          headSubst' <- bindHeadSubst v (CATm tmA') headSubst
          Right (s', headSubst')
        (GP_Ty _, _, _) ->
          Left "unifyObjFlex: expected type argument for constructor parameter"
        (GP_Tm _, _, _) ->
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
      fst <$> foldM step (subst, M.empty) (zip3 params argsA argsB)
  where
    step (s, headSubst) (param, argA, argB) =
      case (param, argA, argB) of
        (GP_Ty v, CAObj tyA, CAObj tyB) -> do
          s' <- unifyObjFlex tt tmCtx flex s tyA tyB
          tyA' <- applySubstObj tt s' tyA
          headSubst' <- bindHeadSubst v (CAObj tyA') headSubst
          Right (s', headSubst')
        (GP_Tm v, CATm tmA, CATm tmB) -> do
          expectedSort <- applyHeadSubstObj tt (structuralConvEnv tt) tmCtx headSubst (tmvSort v)
          s' <- unifyTm tt tmCtx flex s expectedSort tmA tmB
          tmA' <- applySubstTm tt s' expectedSort tmA
          headSubst' <- bindHeadSubst v (CATm tmA') headSubst
          Right (s', headSubst')
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
  if normalizedDiagramHasBinderArgs (unTerm lhs) || normalizedDiagramHasBinderArgs (unTerm rhs)
    then do
      lhsExpr <- diagramToTermExpr tt tmCtxSub expectedSort' lhs
      rhsExpr <- diagramToTermExpr tt tmCtxSub expectedSort' rhs
      unifyTmNorm subst expectedSort' lhsExpr rhsExpr
    else do
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

    normalizedDiagramHasBinderArgs =
      getAny
        . foldDiagram
            (const mempty)
            (const mempty)
            (const mempty)
            (const (Any True))

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
        (TMHead f xs bxs, TMHead g ys bys)
          | f == g
          , length xs == length ys
          , length bxs == length bys -> do
              resolvedL <- canonicalizeHeadAtSubst s currentSort f xs bxs
              resolvedR <- canonicalizeHeadAtSubst s currentSort g ys bys
              let sig = rhaSig resolvedL
              sParam <- unifyGenArgsFlex tt tmCtx tmFlex s (thsParams sig) (rhaStoredCodeArgs resolvedL) (rhaStoredCodeArgs resolvedR)
              sBind <- compareResolvedBinders sParam resolvedL resolvedR
              foldM step sBind (zip3 (thsInputs sig) (map snd (rhaInputs resolvedL)) (map snd (rhaInputs resolvedR)))
          | otherwise -> Left "unifyTm: term head mismatch"
        (TMSplice _ _ _, _) ->
          Left "unifyTm: splice terms are only supported in trusted rewrite compilation"
        (_, TMSplice _ _ _) ->
          Left "unifyTm: splice terms are only supported in trusted rewrite compilation"
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
        TMHead f args bargs -> do
          resolved <- canonicalizeHeadAtSubst s currentSort f args bargs
          mapM_ (uncurry (ensureTmTermSort s)) (rhaInputs resolved)
        TMSplice _ _ _ ->
          Left "unifyTm: splice terms are only supported in trusted rewrite compilation"
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
          Just sig' -> Right (freshenHeadSigAgainstSubst s sig')
      if not (null (thsBinders sig)) || length (thsParams sig) + length (thsInputs sig) /= arity
        then Left "unifyTm: term head arity mismatch"
        else Right ()
      resSort0 <- applySubstObj tt s (thsRes sig)
      resSort <- normalizeInCtx s resSort0
      if resSort == currentSort'
        then Right sig
        else Left "unifyTm: term head result sort mismatch"

    compareResolvedBinders s resolvedL resolvedR =
      foldM
        compareBinder
        s
        (zip (rhaBinderExprArgs resolvedL) (rhaBinderExprArgs resolvedR))

    compareBinder sAcc (TBABody left0, TBABody right0) = do
      left <- canonDiagramRaw =<< applySubstDiagram tt sAcc left0
      right <- canonDiagramRaw =<< applySubstDiagram tt sAcc right0
      if left == right
        then Right sAcc
        else Left "unifyTm: binder argument mismatch"
    compareBinder sAcc (TBAHole left, TBAHole right)
      | left == right =
          Right sAcc
      | otherwise =
          Left "unifyTm: binder-hole mismatch"
    compareBinder _ _ =
      Left "unifyTm: binder argument mismatch"

    canonicalizeHeadAtSubst s currentSort f args bargs = do
      tmCtx1 <- applySubstCtx tt s tmCtx
      currentSort' <- normalizeObjDeepWithCtx tt tmCtx1 =<< applySubstObj tt s currentSort
      expr' <- applySubstExprInCtx tmCtx1 s currentSort' (TMHead f args bargs)
      case expr' of
        TMHead f' args' bargs'
          | f' == f ->
              resolveHeadArgsExpr tt (structuralConvEnv tt) tmCtx1 M.empty currentSort' f args' bargs'
          | otherwise ->
              Left "unifyTm: substituted term head changed unexpectedly"
        _ ->
          Left "unifyTm: substituted term head did not remain a head application"

    applySubstExprInCtx ctx s expectedSort expr = do
      tm <- termExprToDiagram tt ctx expectedSort expr
      tmSub <- applySubstTmInCtx tt ctx s expectedSort tm
      diagramToTermExpr tt ctx expectedSort tmSub

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

    termFromPort diag inputs pid = do
      currentSort <- requirePortSort diag "unifyTm: missing port type in normalized term graph" pid
      readTermPort (reader diag inputs) diag currentSort pid
      where
        reader diag0 inputs0 =
          TermPortReader
            { tprBoundaryLookup = \pid0 -> M.lookup pid0 inputs0
            , tprOnBoundary = \_ i _ -> Right (TMBound i)
            , tprOnEdge = \recur _ _ edge ->
                case ePayload edge of
                  PGen fName args bargs
                    | null bargs -> do
                        sig <-
                          case lookupTmHeadSig tt (dMode diag0) fName of
                            Just sig'
                              | null (thsBinders sig')
                                  && length (thsParams sig') + length (thsInputs sig') == length args + length (eIns edge) ->
                                  Right sig'
                            Just _ -> Left "unifyTm: term head arity mismatch in normalized term graph"
                            Nothing -> Left "unifyTm: unknown term head in normalized term graph"
                        storedArgs <- rebuildStoredArgs (thsParams sig) args
                        inputArgs <- mapM (readInputTerm diag0 recur) (eIns edge)
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
            , tprSingleOutputErr = "unifyTm: normalized term graph must have exactly one output"
            , tprCycleErr = "unifyTm: cycle detected in normalized term graph"
            , tprMissingProducerErr = "unifyTm: missing producer in normalized term graph"
            }
        readInputTerm diag0 recur inp = do
          inpSort <- requirePortSort diag0 "unifyTm: missing port type in normalized term graph" inp
          THATm <$> recur inpSort inp
        boundaryGlobal inp =
          case M.lookup inp inputs of
            Just i -> Right i
            Nothing -> Left "unifyTm: PTmMeta inputs must connect to boundary inputs"
        rebuildStoredArgs params0 args0 = go [] M.empty params0 args0
          where
            go acc _ [] [] = Right (reverse acc)
            go _ _ [] _ = Left "unifyTm: stored arg arity mismatch"
            go _ _ _ [] = Left "unifyTm: stored arg arity mismatch"
            go acc headSubst (param:paramsRest) (arg:argsRest) =
              case (param, arg) of
                (GP_Ty v, CAObj obj) -> do
                  obj' <- applyHeadSubstObj tt (structuralConvEnv tt) tmCtx headSubst obj
                  headSubst' <- bindHeadSubst v (CAObj obj') headSubst
                  go (THAObj obj' : acc) headSubst' paramsRest argsRest
                (GP_Ty _, CATm _) ->
                  Left "unifyTm: expected object-valued stored arg"
                (GP_Tm v, CATm tmArg) -> do
                  sort' <- applyHeadSubstObj tt (structuralConvEnv tt) tmCtx headSubst (tmvSort v)
                  tmExpr <- diagramToTermExpr tt tmCtx sort' tmArg
                  tmDiag <- termExprToDiagram tt tmCtx sort' tmExpr
                  headSubst' <- bindHeadSubst v (CATm tmDiag) headSubst
                  go (THATm tmExpr : acc) headSubst' paramsRest argsRest
                (GP_Tm _, CAObj _) ->
                  Left "unifyTm: expected term-valued stored arg"

    requirePortSort diag err pid =
      case diagramPortObj diag pid of
        Just ty -> Right ty
        Nothing -> Left err

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

freshenHeadSigAgainstSubst :: Subst -> TmHeadSig -> TmHeadSig
freshenHeadSigAgainstSubst subst =
  freshenTmHeadSigAgainst (substDomain subst)

inferExpectedTmSort :: TypeTheory -> [Obj] -> Subst -> TermDiagram -> TermDiagram -> Either Text Obj
inferExpectedTmSort tt tmCtx subst lhs rhs =
  case inferTmSortFromDiagram tt subst lhs of
    Right ty -> Right ty
    Left _ -> inferTmSortFromDiagram tt subst rhs

inferTmSortFromDiagram :: TypeTheory -> Subst -> TermDiagram -> Either Text Obj
inferTmSortFromDiagram tt subst tm =
  case dOut (unTerm tm) of
    [pid] ->
      case diagramPortObj (unTerm tm) pid of
        Nothing -> Left "inferTmSortFromDiagram: missing output port type"
        Just ty -> applySubstObj tt subst ty
    _ -> Left "inferTmSortFromDiagram: term diagram must have exactly one output"

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
      boundSet = hostBoundGlobalsExpr rhs
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
  renameTermGlobalsPartial ren rhs

occursTmVarExpr :: TmVar -> TermExpr -> Bool
occursTmVarExpr v =
  S.member v . freeTmVarsExpr

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
