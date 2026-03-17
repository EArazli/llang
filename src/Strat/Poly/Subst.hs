{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Subst
  ( Subst
  , mkSubst
  , lookupCodeMeta
  , lookupTmMeta
  , insertCodeMeta
  , insertTmMeta
  , codeBindings
  , tmBindings
  , emptySubst
  , substIsEmpty
  , substDomain
  , bindHeadSubst
  , TermSubstOps(..)
  , applySubstObjWith
  , applySubstTmWith
  , applySubstTmInCtxWith
  , applySubstDiagramWith
  , applySubstCtxWith
  , normalizeSubstWith
  , composeSubstWith
  ) where

import Control.Monad (foldM)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.IntMap.Strict as IM
import Strat.Poly.Alpha (freshenCtorSigAgainstWithMaps, freshenTmHeadSigAgainst)
import Strat.Poly.Graph
  ( Diagram(..)
  , Edge(..)
  , EdgePayload(..)
  , diagramPortObj
  , weakenDiagramTmCtxTo
  )
import Strat.Poly.ModeTheory (meSrc, meTgt)
import Strat.Poly.Names (GenName)
import Strat.Poly.Obj
import Strat.Poly.ObjClassifier (modeClassifierMode)
import Strat.Poly.Tele (CtorSig(..), GenParam(..))
import Strat.Poly.Term.AST (TermBinderArg(..), TermExpr(..), TermHeadArg(..))
import Strat.Poly.Traversal (traverseDiagram)
import Strat.Poly.TypeTheory (TmHeadSig(..), TypeTheory(..))

newtype Subst = Subst
  { unSubst :: M.Map TmVar CodeArg
  }
  deriving (Eq, Ord, Show)

substIsEmpty :: Subst -> Bool
substIsEmpty (Subst m) = M.null m

substDomain :: Subst -> S.Set TmVar
substDomain = M.keysSet . unSubst

data TermSubstOps = TermSubstOps
  { tsoNormalizeObj :: [Obj] -> Obj -> Either Text Obj
  , tsoNormalizeTermDiagram :: [Obj] -> Obj -> TermDiagram -> Either Text TermDiagram
  , tsoDiagramToTermExpr :: [Obj] -> Obj -> TermDiagram -> Either Text TermExpr
  , tsoTermExprToDiagram :: [Obj] -> Obj -> TermExpr -> Either Text TermDiagram
  , tsoNormalizeCtx :: [Obj] -> Either Text [Obj]
  , tsoRequireHeadSig :: [Obj] -> Obj -> GenName -> [TermHeadArg] -> [TermBinderArg] -> Either Text TmHeadSig
  , tsoResolveHeadArgs :: [Obj] -> Obj -> GenName -> [TermHeadArg] -> [TermBinderArg] -> Either Text ([TermHeadArg], [TermBinderArg])
  , tsoApplyHeadSubstObj :: [Obj] -> M.Map TmVar CodeArg -> Obj -> Either Text Obj
  , tsoInstantiateMetaBody :: [Obj] -> TmVar -> [Int] -> TermExpr -> Either Text TermExpr
  }

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
    Just old
      | not (sameCategory old arg) ->
          Left
            ( "insertMeta: category conflict for metavariable "
                <> tmvName v
                <> " (existing "
                <> categoryName old
                <> ", new "
                <> categoryName arg
                <> ")"
            )
    _ ->
      Right subst { unSubst = M.insert v arg (unSubst subst) }

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

bindHeadSubst :: TmVar -> CodeArg -> M.Map TmVar CodeArg -> Either Text (M.Map TmVar CodeArg)
bindHeadSubst v arg subst =
  case M.lookup v subst of
    Nothing -> Right (M.insert v arg subst)
    Just old
      | sameCategory old arg -> Right subst
      | otherwise -> Left "term substitution: inconsistent generator-parameter substitution category"

sameCategory :: CodeArg -> CodeArg -> Bool
sameCategory (CAObj _) (CAObj _) = True
sameCategory (CATm _) (CATm _) = True
sameCategory _ _ = False

categoryName :: CodeArg -> Text
categoryName binding =
  case binding of
    CAObj _ -> "type-level"
    CATm _ -> "term-level"

applySubstObjWith :: TermSubstOps -> TypeTheory -> Subst -> Obj -> Either Text Obj
applySubstObjWith ops tt subst ty = do
  raw <- goTy S.empty ty
  tmCtx <- inferObjTmCtx raw
  tsoNormalizeObj ops tmCtx raw
  where
    inferObjTmCtx o = do
      let ctxs = collectObjCtxs o
      foldM mergeTermCtx [] ctxs

    collectObjCtxs Obj { objCode = code } = collectCodeCtxs code

    collectCodeCtxs c =
      case c of
        CTMeta _ -> []
        CTLift _ inner -> collectCodeCtxs inner
        CTCon _ args -> concatMap collectArgCtxs args

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
              Just sig0 ->
                let (sig, _, _) = freshenCtorSigAgainstWithMaps (substDomain subst) sig0
                 in if length (csParams sig) /= length args
                      then Left "applySubstObj: type constructor arity mismatch"
                      else fst <$> foldM (goArgBySig seen) ([], M.empty) (zip (csParams sig) args)
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

    goArgBySig seen (acc, headSubst) (param, arg) =
      case (param, arg) of
        (GP_Ty v, CAObj innerTy) -> do
          innerTy' <- goTy seen innerTy
          headSubst' <- bindHeadSubst v (CAObj innerTy') headSubst
          Right (acc <> [CAObj innerTy'], headSubst')
        (GP_Tm v, CATm tmArg) -> do
          sort' <- tsoApplyHeadSubstObj ops (dTmCtx (unTerm tmArg)) headSubst (tmvSort v)
          tmArg' <- applySubstTmWith ops tt subst sort' tmArg
          headSubst' <- bindHeadSubst v (CATm tmArg') headSubst
          Right (acc <> [CATm tmArg'], headSubst')
        (GP_Ty _, CATm _) ->
          Left "applySubstObj: expected type argument for constructor parameter"
        (GP_Tm _, CAObj _) ->
          Left "applySubstObj: expected term argument for constructor parameter"

    goArgNoSig seen arg =
      case arg of
        CAObj innerTy -> CAObj <$> goTy seen innerTy
        CATm tmArg -> do
          sort <- inferTmSortFromDiagramWith ops tt subst tmArg
          CATm <$> applySubstTmWith ops tt subst sort tmArg

applySubstTmWith :: TermSubstOps -> TypeTheory -> Subst -> Obj -> TermDiagram -> Either Text TermDiagram
applySubstTmWith ops tt subst expectedSort tm =
  applySubstTmInCtxWith ops tt (dTmCtx (unTerm tm)) subst expectedSort tm

applySubstDiagramWith :: TermSubstOps -> TypeTheory -> Subst -> Diagram -> Either Text Diagram
applySubstDiagramWith ops tt subst =
  traverseDiagram onDiag onPayload onCodeArg pure
  where
    onDiag d = do
      dPortObj' <- IM.traverseWithKey (\_ ty -> applySubstObjWith ops tt subst ty) (dPortObj d)
      dTmCtx' <- mapM (applySubstObjWith ops tt subst) (dTmCtx d)
      pure d { dTmCtx = dTmCtx', dPortObj = dPortObj' }

    onPayload payload =
      case payload of
        PGen g args bargs ->
          pure (PGen g args bargs)
        PTmMeta v -> do
          sort' <- applySubstObjWith ops tt subst (tmvSort v)
          pure (PTmMeta (v { tmvSort = sort' }))
        PTmLit lit ->
          pure (PTmLit lit)
        other ->
          pure other

    onCodeArg arg =
      case arg of
        CAObj obj -> CAObj <$> applySubstObjWith ops tt subst obj
        CATm tmArg -> do
          sort <- inferTmSortFromDiagramWith ops tt subst tmArg
          CATm <$> applySubstTmWith ops tt subst sort tmArg

applySubstTmInCtxWith
  :: TermSubstOps
  -> TypeTheory
  -> [Obj]
  -> Subst
  -> Obj
  -> TermDiagram
  -> Either Text TermDiagram
applySubstTmInCtxWith ops tt tmCtx subst expectedSort tm = do
  tmCtx0 <- applySubstCtxWith ops tt subst tmCtx
  tmCtx' <- tsoNormalizeCtx ops tmCtx0
  expectedSort0 <- applySubstObjWith ops tt subst expectedSort
  expectedSort' <- tsoNormalizeObj ops tmCtx' expectedSort0
  tmGraph0 <- applySubstDiagramWith ops tt subst (unTerm tm)
  tmGraphCtx <- tsoNormalizeCtx ops (dTmCtx tmGraph0)
  let tmGraph1 = tmGraph0 { dTmCtx = tmGraphCtx }
  tmGraph <-
    case weakenDiagramTmCtxTo tmCtx' tmGraph1 of
      Left err ->
        Left
          ( err
              <> " (target="
              <> T.pack (show tmCtx')
              <> ", image="
              <> T.pack (show (dTmCtx tmGraph1))
              <> ")"
          )
      Right tmGraph ->
        Right tmGraph
  let tmSub = TermDiagram tmGraph
  expr <- tsoDiagramToTermExpr ops tmCtx' expectedSort' tmSub
  (tmCtxOut, expr') <- substituteTermExprMetasWith ops tt subst tmCtx' expectedSort' expr
  expectedSortOut <- tsoNormalizeObj ops tmCtxOut expectedSort0
  tm' <- tsoTermExprToDiagram ops tmCtxOut expectedSortOut expr'
  tsoNormalizeTermDiagram ops tmCtxOut expectedSortOut tm'

applySubstCtxWith :: TermSubstOps -> TypeTheory -> Subst -> Context -> Either Text Context
applySubstCtxWith ops tt subst = mapM (applySubstObjWith ops tt subst)

normalizeSubstWith :: TermSubstOps -> TypeTheory -> Subst -> Either Text Subst
normalizeSubstWith ops tt subst = do
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
          t' <- applySubstObjWith ops tt subst t
          pure (v, CAObj t')
        CATm t -> do
          sort' <- applySubstObjWith ops tt subst (tmvSort v)
          t' <- applySubstTmWith ops tt subst sort' t
          pure (v { tmvSort = sort' }, CATm t')

    isIdentity v binding =
      case binding of
        CAObj t -> t == OVar v
        CATm t -> isTmIdentity v t

composeSubstWith :: TermSubstOps -> TypeTheory -> Subst -> Subst -> Either Text Subst
composeSubstWith ops tt s2 s1 = do
  appliedPairs <- mapM (substPair s2) (allBindings s1)
  let appliedMap = M.fromList appliedPairs
  ensureCategoryCompatible appliedMap (unSubst s2)
  normalizeSubstWith ops tt (Subst (M.union appliedMap (unSubst s2)))
  where
    substPair subst (v, binding) =
      case binding of
        CAObj t -> do
          t' <- applySubstObjWith ops tt subst t
          pure (v, CAObj t')
        CATm t -> do
          sort' <- applySubstObjWith ops tt subst (tmvSort v)
          t' <- applySubstTmWith ops tt subst sort' t
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

substituteTermExprMetasWith
  :: TermSubstOps
  -> TypeTheory
  -> Subst
  -> [Obj]
  -> Obj
  -> TermExpr
  -> Either Text ([Obj], TermExpr)
substituteTermExprMetasWith ops tt subst =
  go S.empty
  where
    go seen curCtx currentSort expr =
      case expr of
        TMMeta v args -> do
          sort' <- applySubstObjWith ops tt subst (tmvSort v)
          let v' = v { tmvSort = sort' }
          case lookupTmMeta subst v' of
            Nothing -> Right (curCtx, TMMeta v' args)
            Just tmSub ->
              if v' `S.member` seen
                then Right (curCtx, TMMeta v' args)
                else do
                  subCtx0 <- applySubstCtxWith ops tt subst (dTmCtx (unTerm tmSub))
                  sortSub <- tsoNormalizeObj ops subCtx0 sort'
                  subExpr0 <- tsoDiagramToTermExpr ops subCtx0 sortSub tmSub
                  merged0 <- mergeTermCtx curCtx subCtx0
                  subExpr <- tsoInstantiateMetaBody ops merged0 v' args subExpr0
                  (subCtx, subExpr') <- go (S.insert v' seen) merged0 currentSort subExpr
                  Right (subCtx, subExpr')
        TMBound _ ->
          Right (curCtx, expr)
        TMHead f args bargs -> do
          sig0 <- tsoRequireHeadSig ops curCtx currentSort f args bargs
          let sig = freshenTmHeadSigAgainst (substDomain subst) sig0
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
          binderArgsRev <-
            foldM
              stepBinder
              []
              bargs
          currentSort' <- tsoNormalizeObj ops ctxOut =<< applySubstObjWith ops tt subst currentSort
          let flatArgs = reverse paramArgsRev <> reverse inputArgsRev
          let binderArgs = reverse binderArgsRev
          (flatArgs', binderArgs') <- tsoResolveHeadArgs ops ctxOut currentSort' f flatArgs binderArgs
          Right (ctxOut, TMHead f flatArgs' binderArgs')
        TMSplice _ _ _ ->
          Left "applySubstTm: splice terms are only supported in trusted rewrite compilation"
        TMLit _ ->
          Right (curCtx, expr)

    stepParam seen (ctxAcc, acc, headSubst) (param, arg) =
      case (param, arg) of
        (GP_Ty v, THAObj obj) -> do
          obj' <- tsoNormalizeObj ops ctxAcc =<< applySubstObjWith ops tt subst obj
          headSubst' <- bindHeadSubst v (CAObj obj') headSubst
          Right (ctxAcc, THAObj obj' : acc, headSubst')
        (GP_Ty _, THATm _) ->
          Left "applySubstTm: expected object-valued parameter argument"
        (GP_Tm v, THATm tm0) -> do
          sort0 <- tsoApplyHeadSubstObj ops ctxAcc headSubst (tmvSort v)
          sort' <- tsoNormalizeObj ops ctxAcc =<< applySubstObjWith ops tt subst sort0
          (ctxArg, tm1) <- go seen ctxAcc sort' tm0
          ctxNext <- mergeTermCtx ctxAcc ctxArg
          tmDiag <- tsoTermExprToDiagram ops ctxNext sort' tm1
          headSubst' <- bindHeadSubst v (CATm tmDiag) headSubst
          Right (ctxNext, THATm tm1 : acc, headSubst')
        (GP_Tm _, THAObj _) ->
          Left "applySubstTm: expected term-valued parameter argument"

    stepInput seen headSubst (ctxAcc, acc) (argSort, arg) = do
      sort0 <- tsoApplyHeadSubstObj ops ctxAcc headSubst argSort
      sort' <- tsoNormalizeObj ops ctxAcc =<< applySubstObjWith ops tt subst sort0
      tmExpr <-
        case arg of
          THATm tm0 -> Right tm0
          THAObj _ -> Left "applySubstTm: expected term input argument"
      (ctxArg, argExpr) <- go seen ctxAcc sort' tmExpr
      ctxNext <- mergeTermCtx ctxAcc ctxArg
      Right (ctxNext, THATm argExpr : acc)

    stepBinder acc barg =
      case barg of
        TBABody inner0 -> do
          inner <- applySubstDiagramWith ops tt subst inner0
          Right (TBABody inner : acc)
        TBAHole hole ->
          Right (TBAHole hole : acc)

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

inferTmSortFromDiagramWith :: TermSubstOps -> TypeTheory -> Subst -> TermDiagram -> Either Text Obj
inferTmSortFromDiagramWith ops tt subst tm =
  case dOut (unTerm tm) of
    [pid] ->
      case diagramPortObj (unTerm tm) pid of
        Nothing -> Left "inferTmSortFromDiagram: missing output port type"
        Just ty -> applySubstObjWith ops tt subst ty
    _ -> Left "inferTmSortFromDiagram: term diagram must have exactly one output"

isTmIdentity :: TmVar -> TermDiagram -> Bool
isTmIdentity v tm =
  case IM.elems (dEdges (unTerm tm)) of
    [edge] ->
      case (ePayload edge, eIns edge, eOuts edge, dIn (unTerm tm), dOut (unTerm tm)) of
        (PTmMeta w, [], [outPid], [], [outBoundary]) ->
          outPid == outBoundary && v == w
        _ ->
          False
    _ ->
      False

nth :: [a] -> Int -> Maybe a
nth xs i
  | i < 0 = Nothing
  | otherwise =
      case drop i xs of
        y : _ -> Just y
        [] -> Nothing
