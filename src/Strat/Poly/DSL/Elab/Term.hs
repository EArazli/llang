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
  , elabObjExprWithTables
  , elabObjExprInferOwner
  , elabObjExprInferOwnerWithTables
  , elabTmTerm
  , elabTmTermWithTables
  , lookupTmFunByNameInTables
  , lookupTmFunAnyInTables
  , elabInputShapes
  ) where

import qualified Data.Map.Strict as M
import Data.Text (Text)
import Strat.Poly.DSL.AST
import Strat.Poly.DSL.Elab.Resolve (elabRawModExpr)
import Strat.Poly.DefEq (termExprToDiagramChecked)
import Strat.Poly.Doctrine
import Strat.Poly.ModeTheory
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Obj
import Strat.Poly.ObjClassifier (modeClassifierMode, modeUniverseObj)
import Strat.Poly.ObjResolve
  ( resolveTypeRefInClassifierInTables
  , resolveTypeRefInClassifierMaybeInTables
  )
import Strat.Poly.TermExpr (TermExpr(..))
import Strat.Poly.TypeTheory (TypeParamSig(..), TmFunSig(..))

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

elabTmDeclVar :: Doctrine -> ModeName -> [TmVar] -> RawTmVarDecl -> Either Text TmVar
elabTmDeclVar doc defaultMode tyVars decl = do
  sortTy <-
    case elabObjExpr doc tyVars [] M.empty defaultMode (rtvdSort decl) of
      Right ty -> Right ty
      Left _ -> elabObjExprInferOwner doc tyVars [] M.empty (rtvdSort decl)
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
              tmVar <- elabTmDeclVar doc defaultMode tyAcc tmDecl
              go tyAcc (tmVar:tmAcc) (GP_Tm tmVar : paramAcc) rest

buildTypeTemplateBinders
  :: Doctrine
  -> M.Map ModeName ModeName
  -> [TypeParamSig]
  -> [RawParamDecl]
  -> Either Text ([GenParam], [TmVar], [TmVar])
buildTypeTemplateBinders tgt modeMap sigParams decls = do
  if length sigParams /= length decls
    then Left "morphism: type mapping binder arity mismatch"
    else go [] [] [] (zip sigParams decls)
  where
    go tyAcc tmAcc tmplAcc [] =
      Right (reverse tmplAcc, reverse tyAcc, reverse tmAcc)
    go tyAcc tmAcc tmplAcc ((sigParam, decl):rest) =
      case (sigParam, decl) of
        (TPS_Ty srcMode, RPDType tyDecl) -> do
          expectedMode <- lookupMappedMode srcMode
          tyVar <- resolveTyVarDecl tgt expectedMode tyDecl
          ensureFreshName tyAcc tmAcc (tmvName tyVar)
          go (tyVar:tyAcc) tmAcc (GP_Ty tyVar:tmplAcc) rest
        (TPS_Tm srcSort, RPDTerm tmDecl) -> do
          expectedMode <- lookupMappedMode (objOwnerMode srcSort)
          tmSort <- elabObjExpr tgt (reverse tyAcc) (reverse tmAcc) M.empty expectedMode (rtvdSort tmDecl)
          if objOwnerMode tmSort /= expectedMode
            then Left "morphism: type mapping term binder mode mismatch"
            else Right ()
          ensureFreshName tyAcc tmAcc (rtvdName tmDecl)
          let tmVar = TmVar { tmvName = rtvdName tmDecl, tmvSort = tmSort, tmvScope = 0, tmvOwnerMode = Nothing }
          go tyAcc (tmVar:tmAcc) (GP_Tm tmVar:tmplAcc) rest
        (TPS_Ty _, _) ->
          Left "morphism: type mapping binder kind mismatch"
        (TPS_Tm _, _) ->
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
  tys <- mapM (elabObjExprWithTables doc ctorTables tyVars tmVars tmBound expectedMode) ctx
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
elabObjExpr doc tyVars tmVars tmBound expectedOwnerMode expr = do
  ctorTables <- deriveCtorTables doc
  elabObjExprWithTables doc ctorTables tyVars tmVars tmBound expectedOwnerMode expr

elabObjExprWithTables
  :: Doctrine
  -> CtorTables
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> ModeName
  -> RawPolyObjExpr
  -> Either Text Obj
elabObjExprWithTables doc ctorTables tyVars tmVars tmBound expectedOwnerMode expr =
  case expr of
    RPTVar name -> do
      case [v | v <- tyVars, tmvName v == name] of
        [v] -> do
          ownerMode <- ownerModeForTypeMeta doc v
          if ownerMode == expectedOwnerMode
            then Right Obj { objOwnerMode = expectedOwnerMode, objCode = CTMeta (tmVarToObjVar v) }
            else Left "type variable mode mismatch"
        (_:_:_) -> Left ("duplicate type variable name: " <> name)
        [] -> do
          ref <-
            resolveTypeRefInClassifierInTables
              doc
              ctorTables
              expectedOwnerMode
              classifierMode
              RawTypeRef
                { rtrMode = Nothing
                , rtrName = name
                }
          params <- lookupCtorSigForOwnerInTables doc ctorTables expectedOwnerMode ref
          if null params
            then Right Obj { objOwnerMode = expectedOwnerMode, objCode = CTCon ref [] }
            else Left "type constructor arity mismatch"
    RPTMod rawMe innerRaw -> do
      me <- elabRawModExpr (dModes doc) rawMe
      if meTgt me == expectedOwnerMode
        then Right ()
        else Left "modality application target/object mode mismatch"
      codeLift <- classifierLiftForModExpr (dModes doc) me
      inner <- elabObjExprWithTables doc ctorTables tyVars tmVars tmBound (meSrc me) innerRaw
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
          inner <- elabObjExprWithTables doc ctorTables tyVars tmVars tmBound (meSrc me) innerRaw
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
          params <- lookupCtorSigForOwnerInTables doc ctorTables expectedOwnerMode ref
          if length params /= length args
            then Left "type constructor arity mismatch"
            else do
              args' <- mapM (elabOneArg params) (zip params args)
              Right Obj { objOwnerMode = expectedOwnerMode, objCode = CTCon ref args' }
  where
    classifierMode = modeClassifierMode (dModes doc) expectedOwnerMode

    elabOneArg _ (TPS_Ty m, rawArg) = do
      argTy <- elabObjExprWithTables doc ctorTables tyVars tmVars tmBound m rawArg
      if objOwnerMode argTy == m
        then Right (CAObj argTy)
        else Left "type constructor argument mode mismatch"
    elabOneArg _ (TPS_Tm sortTy, rawArg) = do
      tmArg <- elabTmTermWithTables doc ctorTables tyVars tmVars tmBound (Just sortTy) rawArg
      Right (CATm tmArg)

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
elabObjExprInferOwner doc tyVars tmVars tmBound expr = do
  ctorTables <- deriveCtorTables doc
  elabObjExprInferOwnerWithTables doc ctorTables tyVars tmVars tmBound expr

elabObjExprInferOwnerWithTables
  :: Doctrine
  -> CtorTables
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> RawPolyObjExpr
  -> Either Text Obj
elabObjExprInferOwnerWithTables doc ctorTables tyVars tmVars tmBound expr =
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
    attempts = [ (m, elabObjExprWithTables doc ctorTables tyVars tmVars tmBound m expr) | m <- modes ]
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
elabTmTerm doc tyVars tmVars tmBound mExpected raw = do
  ctorTables <- deriveCtorTables doc
  elabTmTermWithTables doc ctorTables tyVars tmVars tmBound mExpected raw

elabTmTermWithTables
  :: Doctrine
  -> CtorTables
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> Maybe Obj
  -> RawPolyObjExpr
  -> Either Text TermDiagram
elabTmTermWithTables doc ctorTables _tyVars tmVars tmBound mExpected raw =
  do
    ttDoc <- doctrineTypeTheoryFromTables doc ctorTables
    (expr, inferredSort) <- elabExpr ctorTables mExpected raw
    let expectedSort = maybe inferredSort id mExpected
    tmCtx <- mkTmCtx
    termExprToDiagramChecked ttDoc tmCtx expectedSort expr
  where
    elabExpr ctorTables mExp tmRaw =
      case tmRaw of
        RPTMod _ _ -> Left "term arguments do not support modality application"
        RPTVar name ->
          case M.lookup name tmBound of
            Just (idx, sortTy) -> Right (TMBound idx, sortTy)
            Nothing ->
              case [v | v <- tmVars, tmvName v == name] of
                [v] -> Right (TMVar v, tmvSort v)
                (_:_:_) -> Left ("duplicate term variable name: " <> name)
                [] ->
                  case mExp of
                    Nothing -> do
                      (funName, sig) <- lookupTmFunAnyInTables doc ctorTables name 0
                      pure (TMFun funName [], tfsRes sig)
                    Just expected -> do
                      (funName, sig) <- lookupTmFunByNameInTables doc ctorTables expected name 0
                      pure (TMFun funName [], tfsRes sig)
        RPTCon rawRef args ->
          case rtrMode rawRef of
            Just _ -> Left "term function names must be unqualified"
            Nothing -> do
              (funName, sig) <-
                case mExp of
                  Just expected -> lookupTmFunByNameInTables doc ctorTables expected (rtrName rawRef) (length args)
                  Nothing -> lookupTmFunAnyInTables doc ctorTables (rtrName rawRef) (length args)
              argExprs <- mapM (\(argSort, argRaw) -> fst <$> elabExpr ctorTables (Just argSort) argRaw) (zip (tfsArgs sig) args)
              pure (TMFun funName argExprs, tfsRes sig)

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

lookupTmFunByNameInTables :: Doctrine -> CtorTables -> Obj -> Text -> Int -> Either Text (TmFunName, TmFunSig)
lookupTmFunByNameInTables doc ctorTables expectedSort name arity =
  let fname = TmFunName name
      sigs = gatherCandidates ctorTables (objOwnerMode expectedSort)
   in case sigs of
        [] -> Left ("unknown term function: " <> name)
        [sig] ->
          if length (tfsArgs sig) == arity
            then Right (fname, sig)
            else Left "term function arity mismatch"
        _ -> Left ("ambiguous term function in mode: " <> name)
  where
    gatherCandidates ctorTables' mode =
      [ TmFunSig
          { tfsArgs = [ ty | InPort ty <- gdDom gd ]
          , tfsRes = res
          }
      | gd <- maybe [] M.elems (M.lookup mode (dGens doc))
      , gdName gd == GenName name
      , not (isTypeDeclGenNameInTables doc ctorTables' mode (ObjName (renderGenName (gdName gd))))
      , null (gdTyVars gd)
      , null (gdTmVars gd)
      , null (gdAttrs gd)
      , all isPort (gdDom gd)
      , [res] <- [gdCod gd]
      ]
    isPort sh =
      case sh of
        InPort _ -> True
        InBinder _ -> False

lookupTmFunAnyInTables :: Doctrine -> CtorTables -> Text -> Int -> Either Text (TmFunName, TmFunSig)
lookupTmFunAnyInTables doc ctorTables name arity =
  case genCandidates ctorTables of
    [] -> Left ("unknown term function: " <> name)
    [single] -> Right single
    _ -> Left ("ambiguous term function: " <> name)
  where
    genCandidates ctorTables' =
      [ ( TmFunName name
        , TmFunSig
            { tfsArgs = [ ty | InPort ty <- gdDom gd ]
            , tfsRes = res
            }
        )
      | modeTable <- M.elems (dGens doc)
      , gd <- M.elems modeTable
      , not (isTypeDeclGenNameInTables doc ctorTables' (gdMode gd) (ObjName (renderGenName (gdName gd))))
      , gdName gd == GenName name
      , null (gdTyVars gd)
      , null (gdTmVars gd)
      , null (gdAttrs gd)
      , all isPort (gdDom gd)
      , [res] <- [gdCod gd]
      , length [ ty | InPort ty <- gdDom gd ] == arity
      ]
    isPort sh =
      case sh of
        InPort _ -> True
        InBinder _ -> False

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
