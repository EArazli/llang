{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.DSL.Elab.Term
  ( provisionalCtorSort
  , resolveTyVarMode
  , resolveTyVarDecl
  , mkTypeMetaVar
  , ownerModeForTypeMeta
  , elabTmDeclVar
  , elabParamDecls
  , buildTypeTemplateBinders
  , elabContext
  , elabContextWithTables
  , elabObjExpr
  , elabObjExprInScope
  , elabObjExprWithTables
  , elabObjExprWithTablesInScope
  , elabObjExprWithTablesImplicitMetas
  , elabObjExprWithTablesImplicitMetasInScope
  , elabObjExprInferOwner
  , elabObjExprInferOwnerInScope
  , elabObjExprInferOwnerWithTables
  , elabObjExprInferOwnerWithTablesInScope
  , elabTmTerm
  , elabTmTermInScope
  , elabTmTermWithTables
  , elabTmTermWithTablesInScope
  , lookupTmFunByNameInTables
  , lookupTmFunAnyInTables
  , elabInputShapes
  ) where

import qualified Data.Map.Strict as M
import Data.Text (Text)
import Strat.Poly.DSL.AST
import Strat.Poly.DSL.Elab.Resolve (elabRawModExpr)
import Strat.Poly.DefEq (normalizeObjDeepWithCtx, termExprToDiagramChecked)
import Strat.Poly.Doctrine
import Strat.Poly.Literal (literalKind)
import Strat.Poly.ModeTheory
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Obj
import Strat.Poly.ObjClassifier (modeClassifierMode, modeUniverseObj)
import Strat.Poly.ObjResolve
  ( resolveTypeRefInClassifierInTables
  , resolveTypeRefInClassifierMaybeInTables
  )
import Strat.Poly.Tele (CtorSig(..), GenParam(..))
import Strat.Poly.TeleArgs (elabTeleArgsSequentialWith)
import Strat.Poly.Term.AST (TermHeadArg(..))
import Strat.Poly.TermExpr (TermExpr(..))
import Strat.Poly.TypeTheory (TmHeadSig(..), literalKindForObj)
import qualified Strat.Poly.UnifyObj as U

provisionalCtorSort :: Doctrine -> ModeName -> Obj
provisionalCtorSort doc mode =
  case modeUniverseObj (dModes doc) mode of
    Just u -> u
    Nothing ->
      case classifierUniverse of
        Just u -> u
        Nothing ->
          Obj
            { objOwnerMode = mode
            , objCode =
                CTCon
                  ObjRef
                    { orMode = modeClassifierMode (dModes doc) mode
                    , orName = ObjName "__obj_meta_sort"
                    }
                  []
            }
  where
    classifierUniverse =
      case
        [ cdUniverse decl
        | decl <- M.elems (mtClassifiedBy (dModes doc))
        , cdClassifier decl == mode
        ]
      of
        (u:_) -> Just u
        [] -> Nothing

resolveTyVarMode :: Doctrine -> ModeName -> RawTyVarDecl -> Either Text ModeName
resolveTyVarMode doc defaultMode decl = do
  let mode = maybe defaultMode ModeName (rtvMode decl)
  ensureMode doc mode
  pure mode

resolveTyVarDecl :: Doctrine -> ModeName -> RawTyVarDecl -> Either Text TmVar
resolveTyVarDecl doc defaultMode decl = do
  mode <- resolveTyVarMode doc defaultMode decl
  mkTypeMetaVar doc mode (rtvName decl)

mkTypeMetaVar :: Doctrine -> ModeName -> Text -> Either Text TmVar
mkTypeMetaVar doc ownerMode name = do
  universe <-
    case modeUniverseObj (dModes doc) ownerMode of
      Nothing ->
        Left
          ( "type variable `"
              <> name
              <> "`: mode "
              <> renderMode ownerMode
              <> " missing classifiedBy universe"
          )
      Just u ->
        Right u
  pure
    TmVar
      { tmvName = name
      , tmvSort = universe
      , tmvScope = 0
      , tmvOwnerMode = Just ownerMode
      }
  where
    renderMode (ModeName n) = n

ownerModeForTypeMeta :: Doctrine -> TmVar -> Either Text ModeName
ownerModeForTypeMeta doc v =
  case tmvOwnerMode v of
    Just owner
      | M.member owner (mtModes (dModes doc)) ->
          Right owner
      | otherwise ->
          Left
            ( "type metavariable `"
                <> tmvName v
                <> "` has unknown owner mode `"
                <> renderMode owner
                <> "`"
            )
    Nothing ->
      Left
        ( "type metavariable `"
            <> tmvName v
            <> "` is missing an explicit owner mode"
        )
  where
    renderMode (ModeName n) = n

elabTmDeclVar :: Doctrine -> ModeName -> [TmVar] -> [TmVar] -> RawTmVarDecl -> Either Text TmVar
elabTmDeclVar doc defaultMode tyVars tmVars decl = do
  sortTy <-
    case elabObjExpr doc tyVars tmVars M.empty defaultMode (rtvdSort decl) of
      Right ty -> Right ty
      Left _ -> elabObjExprInferOwner doc tyVars tmVars M.empty (rtvdSort decl)
  pure TmVar { tmvName = rtvdName decl, tmvSort = sortTy, tmvScope = 0, tmvOwnerMode = Nothing }

elabParamDecls :: Doctrine -> ModeName -> [RawParamDecl] -> Either Text [GenParam]
elabParamDecls doc defaultMode params = go [] [] [] params
  where
    go _ _ paramAcc [] = Right (reverse paramAcc)
    go tyAcc tmAcc paramAcc (p:rest) =
      case p of
        RPDType tvDecl -> do
          ownerMode <- resolveTyVarMode doc defaultMode tvDecl
          tv <- mkTypeMetaVar doc ownerMode (rtvName tvDecl)
          let name = tmvName tv
          if name `elem` map tmvName tyAcc || name `elem` map tmvName tmAcc
            then Left "duplicate parameter name"
            else go (tv:tyAcc) tmAcc (GP_Ty tv : paramAcc) rest
        RPDTerm tmDecl -> do
          let name = rtvdName tmDecl
          if name `elem` map tmvName tyAcc || name `elem` map tmvName tmAcc
            then Left "duplicate parameter name"
            else do
              tmVar <- elabTmDeclVar doc defaultMode tyAcc tmAcc tmDecl
              go tyAcc (tmVar:tmAcc) (GP_Tm tmVar : paramAcc) rest

buildTypeTemplateBinders
  :: Doctrine
  -> M.Map ModeName ModeName
  -> CtorSig
  -> [RawParamDecl]
  -> Either Text ([GenParam], [TmVar], [TmVar])
buildTypeTemplateBinders tgt modeMap sig decls = do
  if length sigParams /= length decls
    then Left "morphism: type mapping binder arity mismatch"
    else go [] [] [] (zip sigParams decls)
  where
    sigParams = csParams sig

    go tyAcc tmAcc tmplAcc [] =
      Right (reverse tmplAcc, reverse tyAcc, reverse tmAcc)
    go tyAcc tmAcc tmplAcc ((sigParam, decl):rest) =
      case (sigParam, decl) of
        (GP_Ty srcVar, RPDType tyDecl) -> do
          expectedMode <- lookupMappedMode (tmVarOwner srcVar)
          tyVar <- resolveTyVarDecl tgt expectedMode tyDecl
          ensureFreshName tyAcc tmAcc (tmvName tyVar)
          go (tyVar:tyAcc) tmAcc (GP_Ty tyVar:tmplAcc) rest
        (GP_Tm srcVar, RPDTerm tmDecl) -> do
          expectedMode <- lookupMappedMode (objOwnerMode (tmvSort srcVar))
          tmSort <- elabObjExpr tgt (reverse tyAcc) (reverse tmAcc) M.empty expectedMode (rtvdSort tmDecl)
          if objOwnerMode tmSort /= expectedMode
            then Left "morphism: type mapping term binder mode mismatch"
            else Right ()
          ensureFreshName tyAcc tmAcc (rtvdName tmDecl)
          let tmVar = TmVar { tmvName = rtvdName tmDecl, tmvSort = tmSort, tmvScope = 0, tmvOwnerMode = Nothing }
          go tyAcc (tmVar:tmAcc) (GP_Tm tmVar:tmplAcc) rest
        (GP_Ty _, _) ->
          Left "morphism: type mapping binder kind mismatch"
        (GP_Tm _, _) ->
          Left "morphism: type mapping binder kind mismatch"

    ensureFreshName tyAcc tmAcc name =
      let tyNames = map tmvName tyAcc
          tmNames = map tmvName tmAcc
       in if name `elem` tyNames || name `elem` tmNames
            then Left "morphism: duplicate type mapping binders"
            else Right ()

    lookupMappedMode srcMode =
      case M.lookup srcMode modeMap of
        Nothing -> Left "morphism: missing mode mapping"
        Just tgtMode -> Right tgtMode

elabContext :: Doctrine -> ModeName -> [TmVar] -> [TmVar] -> M.Map Text (Int, Obj) -> RawPolyContext -> Either Text Context
elabContext doc expectedMode tyVars tmVars tmBound ctx = do
  ctorTables <- deriveCtorTables doc
  elabContextWithTables doc ctorTables expectedMode tyVars tmVars tmBound ctx

elabContextWithTables
  :: Doctrine
  -> CtorTables
  -> ModeName
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> RawPolyContext
  -> Either Text Context
elabContextWithTables doc ctorTables expectedMode tyVars tmVars tmBound ctx = do
  tys <- mapM (elabObjExprWithTablesInScope M.empty doc ctorTables tyVars tmVars tmBound expectedMode) ctx
  let bad = filter (\ty -> objOwnerMode ty /= expectedMode) tys
  if null bad
    then Right tys
    else Left "boundary type must match generator mode"

elabObjExpr
  :: Doctrine
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> ModeName
  -> RawPolyObjExpr
  -> Either Text Obj
elabObjExpr = elabObjExprInScope M.empty

elabObjExprInScope
  :: M.Map Text Obj
  -> Doctrine
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> ModeName
  -> RawPolyObjExpr
  -> Either Text Obj
elabObjExprInScope typeScope doc tyVars tmVars tmBound expectedOwnerMode expr = do
  ctorTables <- deriveCtorTables doc
  elabObjExprWithTablesInScope typeScope doc ctorTables tyVars tmVars tmBound expectedOwnerMode expr

data UnknownTypeNamePolicy
  = UnknownTypeIsError
  | UnknownTypeIsImplicitMeta

elabObjExprWithTables
  :: Doctrine
  -> CtorTables
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> ModeName
  -> RawPolyObjExpr
  -> Either Text Obj
elabObjExprWithTables = elabObjExprWithTablesInScope M.empty

elabObjExprWithTablesInScope
  :: M.Map Text Obj
  -> Doctrine
  -> CtorTables
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> ModeName
  -> RawPolyObjExpr
  -> Either Text Obj
elabObjExprWithTablesInScope typeScope doc ctorTables tyVars tmVars tmBound expectedOwnerMode expr =
  elabObjExprWithTables_ typeScope UnknownTypeIsError doc ctorTables tyVars tmVars tmBound expectedOwnerMode expr

elabObjExprWithTablesImplicitMetas
  :: Doctrine
  -> CtorTables
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> ModeName
  -> RawPolyObjExpr
  -> Either Text Obj
elabObjExprWithTablesImplicitMetas = elabObjExprWithTablesImplicitMetasInScope M.empty

elabObjExprWithTablesImplicitMetasInScope
  :: M.Map Text Obj
  -> Doctrine
  -> CtorTables
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> ModeName
  -> RawPolyObjExpr
  -> Either Text Obj
elabObjExprWithTablesImplicitMetasInScope typeScope doc ctorTables tyVars tmVars tmBound expectedOwnerMode expr =
  elabObjExprWithTables_ typeScope UnknownTypeIsImplicitMeta doc ctorTables tyVars tmVars tmBound expectedOwnerMode expr

elabObjExprWithTables_
  :: M.Map Text Obj
  -> UnknownTypeNamePolicy
  -> Doctrine
  -> CtorTables
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> ModeName
  -> RawPolyObjExpr
  -> Either Text Obj
elabObjExprWithTables_ typeScope pol doc ctorTables tyVars tmVars tmBound expectedOwnerMode expr =
  case expr of
    RPLit _ ->
      Left "literal is not allowed in type expressions"
    RPTVar name -> do
      case [v | v <- tyVars, tmvName v == name] of
        [v] -> do
          ownerMode <- ownerModeForTypeMeta doc v
          if ownerMode == expectedOwnerMode
            then Right Obj { objOwnerMode = expectedOwnerMode, objCode = CTMeta v }
            else Left "type variable mode mismatch"
        (_:_:_) -> Left ("duplicate type variable name: " <> name)
        [] -> do
          case M.lookup name typeScope of
            Just scoped ->
              if objOwnerMode scoped == expectedOwnerMode
                then Right scoped
                else Left "type alias mode mismatch"
            Nothing -> do
              mRef <-
                resolveTypeRefInClassifierMaybeInTables
                  doc
                  ctorTables
                  expectedOwnerMode
                  classifierMode
                  RawTypeRef
                    { rtrMode = Nothing
                    , rtrName = name
                    }
              case mRef of
                Just ref -> do
                  sig <- lookupCtorSigForOwnerInTables doc ctorTables expectedOwnerMode ref
                  if null (csParams sig)
                    then Right Obj { objOwnerMode = expectedOwnerMode, objCode = CTCon ref [] }
                    else Left "type constructor arity mismatch"
                Nothing ->
                  case pol of
                    UnknownTypeIsError -> Left ("unknown type variable: " <> name)
                    UnknownTypeIsImplicitMeta -> do
                      tv <- mkTypeMetaVar doc expectedOwnerMode name
                      Right Obj { objOwnerMode = expectedOwnerMode, objCode = CTMeta tv }
    RPTMod rawMe innerRaw -> do
      me <- elabRawModExpr (dModes doc) rawMe
      if meTgt me == expectedOwnerMode
        then Right ()
        else Left "modality application target/object mode mismatch"
      codeLift <- classifierLiftForModExpr (dModes doc) me
      inner <- elabObjExprWithTables_ typeScope pol doc ctorTables tyVars tmVars tmBound (meSrc me) innerRaw
      if objOwnerMode inner /= meSrc me
        then Left "modality application source/argument mode mismatch"
        else
          normalizeObjExpr
            (dModes doc)
            Obj
              { objOwnerMode = expectedOwnerMode
              , objCode = CTLift codeLift (objCode inner)
              }
    RPTCon rawRef args -> do
      case asModalityCall rawRef args of
        Just (rawMe, innerRaw) -> do
          me <- elabRawModExpr (dModes doc) rawMe
          if meTgt me == expectedOwnerMode
            then Right ()
            else Left "modality application target/object mode mismatch"
          codeLift <- classifierLiftForModExpr (dModes doc) me
          inner <- elabObjExprWithTables_ typeScope pol doc ctorTables tyVars tmVars tmBound (meSrc me) innerRaw
          if objOwnerMode inner /= meSrc me
            then Left "modality application source/argument mode mismatch"
            else
              normalizeObjExpr
                (dModes doc)
                Obj
                  { objOwnerMode = expectedOwnerMode
                  , objCode = CTLift codeLift (objCode inner)
                  }
        Nothing -> do
          ref <- resolveTypeRefInClassifierInTables doc ctorTables expectedOwnerMode classifierMode rawRef
          sig <- lookupCtorSigForOwnerInTables doc ctorTables expectedOwnerMode ref
          if length (csParams sig) /= length args
            then Left "type constructor arity mismatch"
            else do
              tt <- doctrineElabTypeTheoryFromTables doc ctorTables
              (args', _) <-
                elabTeleArgsSequentialWith
                  tt
                  (\v rawArg -> do
                    let ownerMode = tmVarOwner v
                    argTy <- elabObjExprWithTables_ typeScope pol doc ctorTables tyVars tmVars tmBound ownerMode rawArg
                    if objOwnerMode argTy == ownerMode
                      then Right argTy
                      else Left "type constructor argument mode mismatch"
                  )
                  (\expectedSort _ rawArg ->
                    elabTmTermWithTablesInScope typeScope doc ctorTables tyVars tmVars tmBound (Just expectedSort) rawArg
                  )
                  (csParams sig)
                  args
              Right Obj { objOwnerMode = expectedOwnerMode, objCode = CTCon ref args' }
  where
    classifierMode = modeClassifierMode (dModes doc) expectedOwnerMode

    asModalityCall rawRef0 args0 =
      case (rtrMode rawRef0, rtrName rawRef0, args0) of
        (Nothing, name, [inner]) ->
          if hasModality name
            then Just (RMComp [name], inner)
            else Nothing
        (Just modeTok, name, [inner]) ->
          if hasQualifiedType modeTok name
            then Nothing
            else
              if hasModality modeTok && hasModality name
                then Just (RMComp [modeTok, name], inner)
                else Nothing
        _ -> Nothing
    hasModality tok = M.member (ModName tok) (mtDecls (dModes doc))
    hasQualifiedType modeTok tyTok =
      case
        resolveTypeRefInClassifierMaybeInTables
          doc
          ctorTables
          expectedOwnerMode
          classifierMode
          RawTypeRef
            { rtrMode = Just modeTok
            , rtrName = tyTok
            }
      of
        Right (Just _) -> True
        _ -> False

elabObjExprInferOwner
  :: Doctrine
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> RawPolyObjExpr
  -> Either Text Obj
elabObjExprInferOwner = elabObjExprInferOwnerInScope M.empty

elabObjExprInferOwnerInScope
  :: M.Map Text Obj
  -> Doctrine
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> RawPolyObjExpr
  -> Either Text Obj
elabObjExprInferOwnerInScope typeScope doc tyVars tmVars tmBound expr = do
  ctorTables <- deriveCtorTables doc
  elabObjExprInferOwnerWithTablesInScope typeScope doc ctorTables tyVars tmVars tmBound expr

elabObjExprInferOwnerWithTables
  :: Doctrine
  -> CtorTables
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> RawPolyObjExpr
  -> Either Text Obj
elabObjExprInferOwnerWithTables = elabObjExprInferOwnerWithTablesInScope M.empty

elabObjExprInferOwnerWithTablesInScope
  :: M.Map Text Obj
  -> Doctrine
  -> CtorTables
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> RawPolyObjExpr
  -> Either Text Obj
elabObjExprInferOwnerWithTablesInScope typeScope doc ctorTables tyVars tmVars tmBound expr =
  case expr of
    RPTVar name
      | Just obj <- M.lookup name typeScope -> Right obj
    _ ->
      case successes of
        [(_, obj)] -> Right obj
        [] ->
          case failures of
            (err:_) -> Left err
            [] -> Left "unable to infer object mode"
        _ ->
          Left "ambiguous object expression mode (qualify constructors or use a variable with explicit mode)"
  where
    modes = M.keys (mtModes (dModes doc))
    attempts = [ (m, elabObjExprWithTablesInScope typeScope doc ctorTables tyVars tmVars tmBound m expr) | m <- modes ]
    successes = [ (m, obj) | (m, Right obj) <- attempts ]
    failures = [ err | (_, Left err) <- attempts ]

elabTmTerm
  :: Doctrine
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> Maybe Obj
  -> RawPolyObjExpr
  -> Either Text TermDiagram
elabTmTerm = elabTmTermInScope M.empty

elabTmTermInScope
  :: M.Map Text Obj
  -> Doctrine
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> Maybe Obj
  -> RawPolyObjExpr
  -> Either Text TermDiagram
elabTmTermInScope typeScope doc tyVars tmVars tmBound mExpected raw = do
  ctorTables <- deriveCtorTables doc
  elabTmTermWithTablesInScope typeScope doc ctorTables tyVars tmVars tmBound mExpected raw

elabTmTermWithTables
  :: Doctrine
  -> CtorTables
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> Maybe Obj
  -> RawPolyObjExpr
  -> Either Text TermDiagram
elabTmTermWithTables = elabTmTermWithTablesInScope M.empty

elabTmTermWithTablesInScope
  :: M.Map Text Obj
  -> Doctrine
  -> CtorTables
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> Maybe Obj
  -> RawPolyObjExpr
  -> Either Text TermDiagram
elabTmTermWithTablesInScope typeScope doc ctorTables _tyVars tmVars tmBound mExpected raw =
  do
    ttDoc <- doctrineElabTypeTheoryFromTables doc ctorTables
    tmCtx <- mkTmCtx
    (expr, inferredSort) <- elabExpr ttDoc ctorTables tmCtx mExpected raw
    let expectedSort = maybe inferredSort id mExpected
    termExprToDiagramChecked ttDoc tmCtx expectedSort expr
  where
    elabExpr ttDoc ctorTables tmCtx mExp tmRaw =
      case tmRaw of
        RPLit lit ->
          case mExp of
            Just expectedSort0 -> do
              expectedSort <- normalizeObjDeepWithCtx ttDoc tmCtx expectedSort0
              case literalKindForObj ttDoc expectedSort of
                Just expectedKind
                  | expectedKind == literalKind lit ->
                      Right (TMLit lit, expectedSort)
                  | otherwise ->
                      Left "literal kind does not match expected term sort"
                Nothing ->
                  Left "expected term sort does not admit literals"
            Nothing ->
              Left "cannot infer sort for literal term"
        RPTMod _ _ -> Left "term arguments do not support modality application"
        RPTVar name ->
          case M.lookup name tmBound of
            Just (idx, sortTy) -> Right (TMBound idx, sortTy)
            Nothing ->
              case [v | v <- tmVars, tmvName v == name] of
                [v] -> Right (TMMeta v (defaultMetaArgs tmCtx v), tmvSort v)
                (_:_:_) -> Left ("duplicate term variable name: " <> name)
                [] ->
                  case mExp of
                    Nothing -> do
                      (funName, sig) <- lookupTmFunAnyInTables doc ctorTables name 0
                      pure (TMGen funName [], thsRes sig)
                    Just expected -> do
                      (funName, sig) <- lookupTmFunByNameInTables doc ctorTables expected name 0
                      pure (TMGen funName [], thsRes sig)
        RPTCon rawRef args ->
          case rtrMode rawRef of
            Just _ -> Left "term head names must be unqualified"
            Nothing -> do
              (funName, sig) <-
                case mExp of
                  Just expected -> lookupTmFunByNameInTables doc ctorTables expected (rtrName rawRef) (length args)
                  Nothing -> lookupTmFunAnyInTables doc ctorTables (rtrName rawRef) (length args)
              flatArgs <- elabHeadArgs ttDoc ctorTables tmCtx sig args
              pure (TMGen funName flatArgs, thsRes sig)

    elabHeadArgs ttDoc ctorTables tmCtx sig args =
      if length args /= length (thsParams sig) + length (thsInputs sig)
        then Left "term head arity mismatch"
        else do
          let params = zip (thsParams sig) (take (length (thsParams sig)) args)
          let inputs = zip (thsInputs sig) (drop (length (thsParams sig)) args)
          (paramExprs, substAfterParams) <- foldl stepParam (Right ([], U.emptySubst)) params
          inputExprs <- fmap fst (foldl stepInput (Right ([], substAfterParams)) inputs)
          pure (paramExprs <> inputExprs)
      where
        stepParam acc (param, rawArg) = do
          (flatArgs, substAcc) <- acc
          case param of
            GP_Ty v -> do
              obj <- elabObjExprWithTablesInScope typeScope doc ctorTables [] tmVars M.empty (tmVarOwner v) rawArg
              singleton <- U.mkSubst [(v, CAObj obj)]
              substNext <- U.composeSubst ttDoc singleton substAcc
              Right (flatArgs <> [THAObj obj], substNext)
            GP_Tm v -> do
              expectedSort <- U.applySubstObj ttDoc substAcc (tmvSort v)
              (tmExpr, _) <- elabExpr ttDoc ctorTables tmCtx (Just expectedSort) rawArg
              tmDiag <- termExprToDiagramChecked ttDoc tmCtx expectedSort tmExpr
              singleton <- U.mkSubst [(v, CATm tmDiag)]
              substNext <- U.composeSubst ttDoc singleton substAcc
              Right (flatArgs <> [THATm tmExpr], substNext)

        stepInput acc (argSort, rawArg) = do
          (flatArgs, substAcc) <- acc
          expectedSort <- U.applySubstObj ttDoc substAcc argSort
          (tmExpr, _) <- elabExpr ttDoc ctorTables tmCtx (Just expectedSort) rawArg
          Right (flatArgs <> [THATm tmExpr], substAcc)

    mkTmCtx =
      if M.null tmBound
        then Right []
        else do
          let idxMap = M.fromList [ (idx, ty) | (idx, ty) <- M.elems tmBound ]
          let maxIdx = maximum (M.keys idxMap)
          mapM
            (\i ->
              case M.lookup i idxMap of
                Just ty -> Right ty
                Nothing -> Left "term argument uses sparse bound term context")
            [0 .. maxIdx]

lookupTmFunByNameInTables :: Doctrine -> CtorTables -> Obj -> Text -> Int -> Either Text (GenName, TmHeadSig)
lookupTmFunByNameInTables doc ctorTables expectedSort name arity =
  let fname = GenName name
      sigs = gatherCandidates ctorTables (objOwnerMode expectedSort)
   in case sigs of
        [] -> Left ("unknown term head: " <> name)
        [sig] ->
          if length (thsParams sig) + length (thsInputs sig) == arity
            then Right (fname, sig)
            else Left "term head arity mismatch"
        _ -> Left ("ambiguous term head in mode: " <> name)
  where
    gatherCandidates ctorTables' mode =
      [ sig
      | gd <- maybe [] M.elems (M.lookup mode (dGens doc))
      , gdName gd == GenName name
      , not (isTypeDeclGenNameInTables doc ctorTables' mode (ObjName (renderGenName (gdName gd))))
      , Just sig <- [tmHeadSigForGenDecl gd]
      ]

lookupTmFunAnyInTables :: Doctrine -> CtorTables -> Text -> Int -> Either Text (GenName, TmHeadSig)
lookupTmFunAnyInTables doc ctorTables name arity =
  case genCandidates ctorTables of
    [] -> Left ("unknown term head: " <> name)
    [single] -> Right single
    _ -> Left ("ambiguous term head: " <> name)
  where
    genCandidates ctorTables' =
      [ (GenName name, sig)
      | modeTable <- M.elems (dGens doc)
      , gd <- M.elems modeTable
      , not (isTypeDeclGenNameInTables doc ctorTables' (gdMode gd) (ObjName (renderGenName (gdName gd))))
      , gdName gd == GenName name
      , Just sig <- [tmHeadSigForGenDecl gd]
      , length (thsParams sig) + length (thsInputs sig) == arity
      ]

elabInputShapes :: Doctrine -> ModeName -> [TmVar] -> [TmVar] -> [RawInputShape] -> Either Text [InputShape]
elabInputShapes doc mode tyVars tmVars shapes = do
  ctorTables <- deriveCtorTables doc
  mapM (elabInputShapeWithTables doc ctorTables mode tyVars tmVars) shapes

elabInputShapeWithTables
  :: Doctrine
  -> CtorTables
  -> ModeName
  -> [TmVar]
  -> [TmVar]
  -> RawInputShape
  -> Either Text InputShape
elabInputShapeWithTables doc ctorTables mode tyVars tmVars shape =
  case shape of
    RIPort rawTy -> InPort <$> elabObjExprWithTables doc ctorTables tyVars tmVars M.empty mode rawTy
    RIBinder binders rawCod -> do
      boundTys <- mapM (\b -> elabObjExprInferOwnerWithTables doc ctorTables tyVars tmVars M.empty (rbvType b)) binders
      let binderPairs = zip binders boundTys
      let tmBinders = [ (rbvName b, ty) | (b, ty) <- binderPairs, objOwnerMode ty /= mode ]
      let termBinders = [ b | (b, ty) <- binderPairs, objOwnerMode ty == mode ]
      let tmCtx = map snd tmBinders
      let tmBound = M.fromList (zipWith (\(nm, ty) idx -> (nm, (idx, ty))) tmBinders [0..])
      bsDom <- mapM (\b -> elabObjExprWithTables doc ctorTables tyVars tmVars tmBound mode (rbvType b)) termBinders
      bsCod <- elabContextWithTables doc ctorTables mode tyVars tmVars tmBound rawCod
      pure (InBinder BinderSig { bsTmCtx = tmCtx, bsDom = bsDom, bsCod = bsCod })

ensureMode :: Doctrine -> ModeName -> Either Text ()
ensureMode doc mode =
  if M.member mode (mtModes (dModes doc))
    then Right ()
    else Left "unknown mode"

renderGenName :: GenName -> Text
renderGenName (GenName n) = n
