{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Surface.Elab
  ( elabSurfaceExpr
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Control.Monad (foldM)

import Strat.Poly.Surface.Spec
import Strat.Poly.Surface.Parse (parseSurfaceExpr)
import Strat.Poly.Doctrine (Doctrine(..), GenDecl(..), TypeSig(..), lookupTypeSig)
import Strat.Poly.ModeTheory (ModeName(..), ModeTheory(..), ModName(..), ModDecl(..), ModExpr(..), VarDiscipline(..), modeDiscipline, allowsDrop, allowsDup, emptyModeTheory)
import Strat.Poly.Names (GenName(..), BoxName(..))
import Strat.Poly.TypeExpr (TypeExpr, TypeName(..), TypeRef(..), TyVar(..), Context, typeMode)
import qualified Strat.Poly.TypeExpr as Ty
import qualified Strat.Poly.UnifyTy as U
import Strat.Poly.Diagram (Diagram(..), idD, diagramDom, diagramCod, freeTyVarsDiagram, freeAttrVarsDiagram, applySubstDiagram)
import Strat.Poly.Attr
import Strat.Poly.Graph
  ( PortId(..)
  , EdgePayload(..)
  , emptyDiagram
  , freshPort
  , addEdgePayload
  , mergePorts
  , validateDiagram
  , shiftDiagram
  , diagramPortType
  , unionDisjointIntMap
  )
import Strat.Poly.DSL.AST (RawPolyTypeExpr(..), RawTypeRef(..), RawModExpr(..))
import Strat.Frontend.Env (ModuleEnv(..), TermDef(..))


type Subst = U.Subst

applySubstTy :: Subst -> TypeExpr -> TypeExpr
applySubstTy = U.applySubstTy emptyModeTheory

applySubstCtx :: Subst -> Context -> Context
applySubstCtx = U.applySubstCtx emptyModeTheory

unifyTyFlex :: S.Set TyVar -> TypeExpr -> TypeExpr -> Either Text Subst
unifyTyFlex = U.unifyTyFlex emptyModeTheory

composeSubst :: Subst -> Subst -> Subst
composeSubst = U.composeSubst emptyModeTheory


-- Public entrypoint

elabSurfaceExpr :: ModuleEnv -> Doctrine -> PolySurfaceDef -> Text -> Either Text Diagram
elabSurfaceExpr menv doc surf src = do
  let spec = psSpec surf
  ast <- parseSurfaceExpr spec src
  ops <- requireStructuralOps doc (psMode surf)
  env0 <- initEnv
  diag <- evalFresh (elabAst menv doc (psMode surf) spec ops env0 ast)
  if M.null (sdUses diag)
    then do
      validateDiagram (sdDiag diag)
      ensureAttrVarNameSortsDiagram (freeAttrVarsDiagram (sdDiag diag))
      pure (sdDiag diag)
    else Left "surface: unresolved variables"


-- Elaboration environment

data ElabEnv = ElabEnv
  { eeVars :: M.Map Text TypeExpr
  , eeVarDefs :: M.Map Text Diagram
  , eeTypeSubst :: Subst
  } deriving (Eq, Show)

initEnv :: Either Text ElabEnv
initEnv = Right (ElabEnv M.empty M.empty M.empty)

elabSurfaceTypeExpr :: Doctrine -> ModeName -> RawPolyTypeExpr -> Either Text TypeExpr
elabSurfaceTypeExpr doc mode expr =
  case expr of
    RPTVar name ->
      Right (Ty.TVar (TyVar { tvName = name, tvMode = mode }))
    RPTMod rawMe innerRaw -> do
      me <- elabRawModExprSurface (dModes doc) rawMe
      inner <- elabSurfaceTypeExpr doc mode innerRaw
      if typeMode inner /= meSrc me
        then Left "surface: modality application source/argument mode mismatch"
        else Ty.normalizeTypeExpr (dModes doc) (Ty.TMod me inner)
    RPTCon rawRef args -> do
      case asModalityCall rawRef args of
        Just (rawMe, innerRaw) -> do
          me <- elabRawModExprSurface (dModes doc) rawMe
          inner <- elabSurfaceTypeExpr doc mode innerRaw
          if typeMode inner /= meSrc me
            then Left "surface: modality application source/argument mode mismatch"
            else Ty.normalizeTypeExpr (dModes doc) (Ty.TMod me inner)
        Nothing -> do
          ref <- resolveTypeRefSurface doc rawRef
          sig <- lookupTypeSig doc ref
          let params = tsParams sig
          if length params /= length args
            then Left "surface: type constructor arity mismatch"
            else do
              args' <- mapM (elabSurfaceTypeExpr doc mode) args
              let argModes = map typeMode args'
              if and (zipWith (==) params argModes)
                then Right (Ty.TCon ref args')
                else Left "surface: type constructor argument mode mismatch"
  where
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
      let mode' = ModeName modeTok
          tyName = TypeName tyTok
       in case M.lookup mode' (dTypes doc) of
            Nothing -> False
            Just table -> M.member tyName table

resolveTypeRefSurface :: Doctrine -> RawTypeRef -> Either Text TypeRef
resolveTypeRefSurface doc raw =
  case rtrMode raw of
    Just modeName -> do
      let mode = ModeName modeName
      if M.member mode (mtModes (dModes doc))
        then Right ()
        else Left "surface: unknown mode"
      let tname = TypeName (rtrName raw)
      case M.lookup mode (dTypes doc) >>= M.lookup tname of
        Nothing -> Left "surface: unknown type constructor"
        Just _ -> Right (TypeRef mode tname)
    Nothing -> do
      let tname = TypeName (rtrName raw)
      let matches =
            [ mode
            | (mode, table) <- M.toList (dTypes doc)
            , M.member tname table
            ]
      case matches of
        [] -> Left "surface: unknown type constructor"
        [mode] -> Right (TypeRef mode tname)
        _ -> Left "surface: ambiguous type constructor (qualify with Mode.)"

elabRawModExprSurface :: ModeTheory -> RawModExpr -> Either Text ModExpr
elabRawModExprSurface mt raw =
  case raw of
    RMId modeName -> do
      let mode = ModeName modeName
      if M.member mode (mtModes mt)
        then Right ModExpr { meSrc = mode, meTgt = mode, mePath = [] }
        else Left ("surface: unknown mode in modality expression: " <> modeName)
    RMComp toks -> do
      path <- mapM requireModName (reverse toks)
      case path of
        [] -> Left "surface: empty modality expression"
        (m0:rest) -> do
          d0 <- requireDecl m0
          tgt <- foldM step (mdTgt d0) rest
          Right
            ModExpr
              { meSrc = mdSrc d0
              , meTgt = tgt
              , mePath = m0 : rest
              }
  where
    requireModName tok =
      let name = ModName tok
       in if M.member name (mtDecls mt)
            then Right name
            else Left ("surface: unknown modality in expression: " <> tok)
    requireDecl name =
      case M.lookup name (mtDecls mt) of
        Nothing -> Left "surface: unknown modality"
        Just decl -> Right decl
    step cur name = do
      decl <- requireDecl name
      if mdSrc decl == cur
        then Right (mdTgt decl)
        else Left "surface: modality composition type mismatch"


-- Diagrams with variable uses and tags

data SurfDiag = SurfDiag
  { sdDiag :: Diagram
  , sdUses :: Uses
  , sdTags :: Tags
  } deriving (Eq, Show)

type Uses = M.Map Text [PortId]

data Tag = TagHole Int
  deriving (Eq, Ord, Show)

type Tags = M.Map Tag [PortId]

emptySurf :: Diagram -> SurfDiag
emptySurf d = SurfDiag d M.empty M.empty

mergeUses :: Uses -> Uses -> Uses
mergeUses = M.unionWith (<> )

shiftUses :: Int -> Uses -> Uses
shiftUses off = M.map (map shiftPort)
  where
    shiftPort (PortId k) = PortId (k + off)

replacePortUses :: PortId -> PortId -> Uses -> Uses
replacePortUses keep drop = M.map (dedupe . map replace)
  where
    replace p = if p == drop then keep else p

mergeTags :: Tags -> Tags -> Tags
mergeTags = M.unionWith (<> )

shiftTags :: Int -> Tags -> Tags
shiftTags off = M.map (map shiftPort)
  where
    shiftPort (PortId k) = PortId (k + off)

replacePortTags :: PortId -> PortId -> Tags -> Tags
replacePortTags keep drop = M.map (dedupe . map replace)
  where
    replace p = if p == drop then keep else p

dedupe :: Ord a => [a] -> [a]
dedupe = go S.empty
  where
    go _ [] = []
    go seen (x:xs)
      | x `S.member` seen = go seen xs
      | otherwise = x : go (S.insert x seen) xs

applySubstSurf :: Subst -> SurfDiag -> SurfDiag
applySubstSurf subst sd = sd { sdDiag = applySubstDiagram emptyModeTheory subst (sdDiag sd) }

unifyCtxFlex :: S.Set TyVar -> Context -> Context -> Either Text Subst
unifyCtxFlex flex ctx1 ctx2
  | length ctx1 /= length ctx2 = Left "surface: context length mismatch"
  | otherwise = foldl step (Right M.empty) (zip ctx1 ctx2)
  where
    step acc (a, b) = do
      s <- acc
      s' <- unifyTyFlex flex (applySubstTy s a) (applySubstTy s b)
      pure (composeSubst s' s)


-- Structural discipline

data StructuralOps = StructuralOps
  { soDiscipline :: VarDiscipline
  , soDup :: Maybe GenDecl
  , soDrop :: Maybe GenDecl
  } deriving (Eq, Show)

requireStructuralOps :: Doctrine -> ModeName -> Either Text StructuralOps
requireStructuralOps doc mode = do
  disc <- modeDiscipline (dModes doc) mode
  dup <-
    if allowsDup disc
      then Just <$> requireGenDecl "dup"
      else Right Nothing
  dropGen <-
    if allowsDrop disc
      then Just <$> requireGenDecl "drop"
      else Right Nothing
  mapM_ ensureDupShape dup
  mapM_ ensureDropShape dropGen
  pure StructuralOps
    { soDiscipline = disc
    , soDup = dup
    , soDrop = dropGen
    }
  where
    requireGenDecl label =
      case M.lookup mode (dGens doc) >>= M.lookup (GenName label) of
        Nothing -> Left ("surface structural: missing " <> label <> " generator")
        Just gen -> Right gen

requireGen :: Doctrine -> ModeName -> Text -> Either Text GenDecl
requireGen doc mode name =
  case M.lookup mode (dGens doc) >>= M.lookup (GenName name) of
    Nothing -> Left ("surface: missing generator " <> name)
    Just gen -> Right gen

ensureDupShape :: GenDecl -> Either Text ()
ensureDupShape gen =
  if not (null (gdAttrs gen))
    then Left "surface: structural generator dup/drop must not declare attributes"
    else
      case (gdTyVars gen, gdDom gen, gdCod gen) of
        ([v], [Ty.TVar v1], [Ty.TVar v2, Ty.TVar v3])
          | v == v1 && v == v2 && v == v3 -> Right ()
        _ -> Left "surface structural: configured dup generator has wrong type"

ensureDropShape :: GenDecl -> Either Text ()
ensureDropShape gen =
  if not (null (gdAttrs gen))
    then Left "surface: structural generator dup/drop must not declare attributes"
    else
      case (gdTyVars gen, gdDom gen, gdCod gen) of
        ([v], [Ty.TVar v1], []) | v == v1 -> Right ()
        _ -> Left "surface structural: configured drop generator has wrong type"



-- Elaboration core

elabAst :: ModuleEnv -> Doctrine -> ModeName -> SurfaceSpec -> StructuralOps -> ElabEnv -> SurfaceAST -> Fresh SurfDiag
elabAst menv doc mode spec cart env ast =
  case ast of
    SAIdent name ->
      case M.lookup name (eeVars env) of
        Just ty -> elabVarRef doc mode env (eeTypeSubst env) name ty
        Nothing -> elabZeroArgGen doc mode env name
    SALit _ -> liftEither (Left "surface: bare literal must be handled by an elaboration rule")
    SAType _ -> liftEither (Left "surface: unexpected type where expression expected")
    SANode ctor args ->
      if ctor == "CALL"
        then elabCall menv doc mode spec cart env args
        else do
          rule <- case M.lookup ctor (ssElabRules spec) of
            Nothing -> liftEither (Left ("surface: missing elaboration rule for " <> ctor))
            Just r -> pure r
          elabNode menv doc mode spec cart env rule args

elabZeroArgGen :: Doctrine -> ModeName -> ElabEnv -> Text -> Fresh SurfDiag
elabZeroArgGen doc mode env name = do
  gen <- liftEither (lookupGen doc mode (GenName name))
  liftEither (ensureDirectGenCallAttrs gen)
  if null (gdDom gen)
    then do
      diag <- genDFromDecl mode env gen Nothing M.empty
      pure (emptySurf diag)
    else liftEither (Left ("surface: unknown variable " <> name))

elabCall :: ModuleEnv -> Doctrine -> ModeName -> SurfaceSpec -> StructuralOps -> ElabEnv -> [SurfaceAST] -> Fresh SurfDiag
elabCall menv doc mode _spec _cart env args =
  case args of
    [SAIdent name, argExpr] -> do
      argDiag <- elabAst menv doc mode _spec _cart env argExpr
      gen <- liftEither (lookupGen doc mode (GenName name))
      buildGenCall doc mode env gen argDiag
    _ -> liftEither (Left "surface: CALL expects name and argument expression")

buildGenCall :: Doctrine -> ModeName -> ElabEnv -> GenDecl -> SurfDiag -> Fresh SurfDiag
buildGenCall _doc mode env gen argDiag = do
  liftEither (ensureDirectGenCallAttrs gen)
  argTypes <- liftEither (diagramCod (sdDiag argDiag))
  renameSubst <- freshSubst (gdTyVars gen)
  let dom0 = applySubstCtx renameSubst (gdDom gen)
  let cod0 = applySubstCtx renameSubst (gdCod gen)
  let dom1 = applySubstCtx (eeTypeSubst env) dom0
  let cod1 = applySubstCtx (eeTypeSubst env) cod0
  let flex = S.union (freeTyVarsDiagram (sdDiag argDiag)) (freeTyVarsCtx dom1)
  subst <- liftEither (unifyCtxFlex flex dom1 argTypes)
  let argDiag' = applySubstSurf subst argDiag
  let cod = applySubstCtx subst cod1
  let argPorts = dOut (sdDiag argDiag')
  let (outPorts, diag1) = allocPorts cod (sdDiag argDiag')
  diag2 <- liftEither (addEdgePayload (PGen (gdName gen) M.empty) argPorts outPorts diag1)
  let diag3 = diag2 { dOut = outPorts }
  liftEither (validateDiagram diag3)
  pure argDiag' { sdDiag = diag3 }
  where
    freeTyVarsCtx = S.unions . map freeTyVarsTy
    freeTyVarsTy ty =
      case ty of
        Ty.TVar v -> S.singleton v
        Ty.TCon _ xs -> S.unions (map freeTyVarsTy xs)

ensureDirectGenCallAttrs :: GenDecl -> Either Text ()
ensureDirectGenCallAttrs gen =
  if null (gdAttrs gen)
    then Right ()
    else Left "surface: generator requires attribute arguments; supply via an elaboration rule/template"

elabNode :: ModuleEnv -> Doctrine -> ModeName -> SurfaceSpec -> StructuralOps -> ElabEnv -> ElabRule -> [SurfaceAST] -> Fresh SurfDiag
elabNode menv doc mode spec cart env rule args = do
  let params = erArgs rule
  if length params /= length args
    then liftEither (Left "surface: elaboration rule arity mismatch")
    else do
      let paramMap = M.fromList (zip params args)
      typeSubst <- liftEither (buildTypeSubst doc mode env paramMap)
      let (binder, bodyIndex, exprInfos) = detectBinder params args
      (childDiags, holeMap) <- elabChildren menv doc mode spec cart env binder bodyIndex exprInfos
      let childList = map snd childDiags
      surf <- evalTemplate menv doc mode spec cart env paramMap typeSubst holeMap childList (erTemplate rule)
      surf' <- applyBinder doc mode cart env binder holeMap surf
      pure surf'


-- Detect binder information

data BinderKind
  = BinderInput Text RawPolyTypeExpr
  | BinderValue Text Int
  deriving (Eq, Show)

data BinderInfo = BinderInfo
  { biName :: Text
  , biKind :: BinderKind
  } deriving (Eq, Show)

detectBinder :: [Text] -> [SurfaceAST] -> (Maybe BinderInfo, Maybe Int, [(Int, SurfaceAST)])
detectBinder params args =
  let indexed = zip3 [0..] params args
      exprInfos0 =
        [ (idx, arg)
        | (idx, _p, arg) <- indexed
        , isExprArg arg
        ]
      bodyIndex = if null exprInfos0 then Nothing else Just (fst (last exprInfos0))
      binder = findBinder indexed exprInfos0 bodyIndex
      exprInfos =
        case binder of
          Nothing -> exprInfos0
          Just (BinderInfo _ _) ->
            [ (idx, arg)
            | (idx, arg) <- exprInfos0
            , not (isBinderIdent exprInfos0 bodyIndex idx indexed)
            ]
  in (binder, bodyIndex, exprInfos)
  where
    isExprArg a =
      case a of
        SAType _ -> False
        SALit _ -> False
        _ -> True

    isBinderIdent exprInfos bodyIdx idx indexed =
      case [ () | (i, _p, arg) <- indexed, i == idx, isIdentArg arg ] of
        [] -> False
        _ ->
          case findBinder indexed exprInfos bodyIdx of
            Just (BinderInfo name _) ->
              case [ p | (i, p, _arg) <- indexed, i == idx ] of
                [pname] -> pname == name
                _ -> False
            Nothing -> False

    isIdentArg arg =
      case arg of
        SAIdent _ -> True
        _ -> False

    findBinder indexed exprInfos bodyIndex =
      case bodyIndex of
        Nothing -> Nothing
        Just bodyIdx ->
          let exprIndices = map fst exprInfos
              tryBinder [] = Nothing
              tryBinder ((idx, pname, arg):rest) =
                case arg of
                  SAIdent varName ->
                    case lookup (idx + 1) [(i, a) | (i, _p, a) <- indexed] of
                      Just (SAType ty) ->
                        Just (BinderInfo pname (BinderInput varName ty))
                      _ ->
                        let exprAfter = filter (> idx) exprIndices
                        in if length exprAfter >= 2 && bodyIdx == last exprAfter
                          then Just (BinderInfo pname (BinderValue varName (head exprAfter)))
                          else tryBinder rest
                  _ -> tryBinder rest
          in tryBinder indexed


-- Elaborate child expressions

type HoleMap = M.Map Int Int

elabChildren :: ModuleEnv -> Doctrine -> ModeName -> SurfaceSpec -> StructuralOps -> ElabEnv -> Maybe BinderInfo -> Maybe Int -> [(Int, SurfaceAST)] -> Fresh ([(Int, SurfDiag)], HoleMap)
elabChildren menv doc mode spec cart env binder bodyIndex exprInfos = do
  let exprIndices = map fst exprInfos
  let holeMap = M.fromList (zip exprIndices [1..])
  childDiags <- mapM (elabOne holeMap) exprInfos
  pure (childDiags, holeMap)
  where
    elabOne hm (idx, expr) = do
      env' <- case (binder, bodyIndex) of
        (Just b, Just bodyIdx) | idx == bodyIdx ->
          extendEnv doc mode env b
        _ -> pure env
      d <- elabAst menv doc mode spec cart env' expr
      pure (idx, d)

extendEnv :: Doctrine -> ModeName -> ElabEnv -> BinderInfo -> Fresh ElabEnv
extendEnv doc mode env (BinderInfo _ (BinderInput varName tyAnn)) = do
  tyAnn' <- liftEither (elabSurfaceTypeExpr doc mode tyAnn)
  if typeMode tyAnn' /= mode
    then liftEither (Left "surface: binder type must be in surface mode")
    else pure ()
  let ty0 = applySubstTy (eeTypeSubst env) tyAnn'
  pure env
    { eeVars = M.insert varName ty0 (eeVars env)
    , eeVarDefs = M.delete varName (eeVarDefs env)
    }
extendEnv _doc mode env (BinderInfo _ (BinderValue varName _)) = do
  fresh <- freshTyVar (TyVar { tvName = varName, tvMode = mode })
  let ty = Ty.TVar fresh
  pure env
    { eeVars = M.insert varName ty (eeVars env)
    , eeVarDefs = M.delete varName (eeVarDefs env)
    }

elabVarRef :: Doctrine -> ModeName -> ElabEnv -> Subst -> Text -> TypeExpr -> Fresh SurfDiag
elabVarRef _doc mode env subst name ty = do
  let ty' = applySubstTy subst ty
  let base0 =
        case M.lookup name (eeVarDefs env) of
          Just def -> emptySurf def
          Nothing -> varSurf mode name ty'
  pure (applySubstSurf subst base0)


-- Template evaluation

evalTemplate :: ModuleEnv -> Doctrine -> ModeName -> SurfaceSpec -> StructuralOps -> ElabEnv -> M.Map Text SurfaceAST -> Subst -> HoleMap -> [SurfDiag] -> TemplateExpr -> Fresh SurfDiag
evalTemplate menv doc mode _spec _cart env paramMap subst holeMap childList templ =
  case templ of
    THole n ->
      case drop (n - 1) childList of
        (sd:_) -> pure (tagHole n sd)
        [] -> liftEither (Left "surface: template hole out of range")
    TVar name -> do
      varName <- case M.lookup name paramMap of
        Just (SAIdent v) -> pure v
        _ -> liftEither (Left "surface: unknown variable placeholder")
      case M.lookup varName (eeVars env) of
        Nothing -> elabZeroArgGen doc mode env varName
        Just ty -> elabVarRef doc mode env subst varName ty
    TTermRef name ->
      case M.lookup name (meTerms menv) of
        Nothing -> liftEither (Left ("surface: unknown term reference @" <> name))
        Just td ->
          if tdDoctrine td /= dName doc
            then liftEither (Left ("surface: term @" <> name <> " doctrine mismatch"))
            else if tdMode td /= mode
              then liftEither (Left ("surface: term @" <> name <> " mode mismatch"))
              else pure (emptySurf (tdDiagram td))
    TId ctx -> do
      ctx'0 <- liftEither (mapM (elabSurfaceTypeExpr doc mode) ctx)
      let ctx' = map (applySubstTy subst) ctx'0
      pure (emptySurf (idD mode ctx'))
    TGen name mArgs mAttrArgs -> do
      gen <- liftEither (lookupGen doc mode (GenName name))
      args0 <- case mArgs of
        Nothing -> pure Nothing
        Just args -> do
          tys <- liftEither (mapM (elabSurfaceTypeExpr doc mode) args)
          pure (Just tys)
      let args' = fmap (map (applySubstTy subst)) args0
      attrs <- liftEither (elabTemplateGenAttrs doc gen paramMap mAttrArgs)
      diag <- genDFromDecl mode env gen args' attrs
      pure (emptySurf diag)
    TBox name inner -> do
      innerDiag <- evalTemplate menv doc mode _spec _cart env paramMap subst holeMap childList inner
      liftEither (boxSurf mode name innerDiag)
    TLoop inner -> do
      innerDiag <- evalTemplate menv doc mode _spec _cart env paramMap subst holeMap childList inner
      liftEither (loopSurf innerDiag)
    TComp a b -> do
      d1 <- evalTemplate menv doc mode _spec _cart env paramMap subst holeMap childList a
      d2 <- evalTemplate menv doc mode _spec _cart env paramMap subst holeMap childList b
      liftEither (compSurf d1 d2)
    TTensor a b -> do
      d1 <- evalTemplate menv doc mode _spec _cart env paramMap subst holeMap childList a
      d2 <- evalTemplate menv doc mode _spec _cart env paramMap subst holeMap childList b
      liftEither (tensorSurf d1 d2)

buildTypeSubst :: Doctrine -> ModeName -> ElabEnv -> M.Map Text SurfaceAST -> Either Text Subst
buildTypeSubst doc mode env paramMap = do
  pairs <- mapM toPair (M.toList paramMap)
  let local = M.fromList (concat pairs)
  pure (M.union local (eeTypeSubst env))
  where
    toPair (name, ast) =
      case ast of
        SAType rawTy -> do
          ty <- elabSurfaceTypeExpr doc mode rawTy
          let var = TyVar { tvName = name, tvMode = mode }
          pure [(var, ty)]
        _ -> pure []

elabTemplateGenAttrs
  :: Doctrine
  -> GenDecl
  -> M.Map Text SurfaceAST
  -> Maybe [TemplateAttrArg]
  -> Either Text AttrMap
elabTemplateGenAttrs doc gen paramMap mArgs =
  case gdAttrs gen of
    [] ->
      case mArgs of
        Nothing -> Right M.empty
        Just _ -> Left "surface: generator does not accept attribute arguments"
    fields -> do
      args <- maybe (Left "surface: missing generator attribute arguments") Right mArgs
      normalized <- normalizeTemplateAttrArgs fields args
      fmap M.fromList (mapM elabOne normalized)
  where
    elabOne (fieldName, fieldSort, termTemplate) = do
      term <- elabTemplateAttrTerm doc fieldSort paramMap termTemplate
      Right (fieldName, term)

normalizeTemplateAttrArgs
  :: [(AttrName, AttrSort)]
  -> [TemplateAttrArg]
  -> Either Text [(AttrName, AttrSort, AttrTemplate)]
normalizeTemplateAttrArgs fields args =
  case (namedArgs, positionalArgs) of
    (_:_, _:_) -> Left "surface: template attribute arguments must be either all named or all positional"
    (_:_, []) -> normalizeNamed namedArgs
    ([], _) -> normalizePos positionalArgs
  where
    namedArgs = [ (name, term) | TAName name term <- args ]
    positionalArgs = [ term | TAPos term <- args ]
    fieldNames = map fst fields
    normalizeNamed named = do
      ensureDistinctText "surface: duplicate generator attribute argument" (map fst named)
      if length named /= length fields
        then Left "surface: generator attribute argument mismatch"
        else Right ()
      if S.fromList (map fst named) == S.fromList fieldNames
        then Right ()
        else Left "surface: generator attribute arguments must cover exactly the declared fields"
      let namedMap = M.fromList named
      traverse
        (\(fieldName, fieldSort) ->
          case M.lookup fieldName namedMap of
            Nothing -> Left "surface: missing generator attribute argument"
            Just term -> Right (fieldName, fieldSort, term))
        fields
    normalizePos positional =
      if length positional /= length fields
        then Left "surface: generator attribute argument mismatch"
        else Right [ (fieldName, fieldSort, term) | ((fieldName, fieldSort), term) <- zip fields positional ]

ensureDistinctText :: Text -> [Text] -> Either Text ()
ensureDistinctText label names =
  if length names == S.size (S.fromList names)
    then Right ()
    else Left label

elabTemplateAttrTerm :: Doctrine -> AttrSort -> M.Map Text SurfaceAST -> AttrTemplate -> Either Text AttrTerm
elabTemplateAttrTerm doc expectedSort paramMap termTemplate =
  case termTemplate of
    ATLIT lit -> do
      ensureLiteralAllowed doc expectedSort lit
      Right (ATLit lit)
    ATHole name ->
      case M.lookup name paramMap of
        Just (SALit lit) -> do
          ensureLiteralAllowed doc expectedSort lit
          Right (ATLit lit)
        Just (SAIdent identName) -> do
          let lit = ALString identName
          ensureLiteralAllowed doc expectedSort lit
          Right (ATLit lit)
        _ -> Left "surface: attribute hole must be bound to a literal or identifier"
    Strat.Poly.Surface.Spec.ATVar name ->
      Right (Strat.Poly.Attr.ATVar (AttrVar name expectedSort))

ensureLiteralAllowed :: Doctrine -> AttrSort -> AttrLit -> Either Text ()
ensureLiteralAllowed doc sortName lit = do
  decl <-
    case M.lookup sortName (dAttrSorts doc) of
      Nothing -> Left "surface: unknown attribute sort"
      Just d -> Right d
  let litKind =
        case lit of
          ALInt _ -> LKInt
          ALString _ -> LKString
          ALBool _ -> LKBool
  case asLitKind decl of
    Just allowed | allowed == litKind -> Right ()
    _ -> Left "surface: attribute sort does not admit this literal kind"


-- Apply binder after template evaluation

applyBinder :: Doctrine -> ModeName -> StructuralOps -> ElabEnv -> Maybe BinderInfo -> HoleMap -> SurfDiag -> Fresh SurfDiag
applyBinder _doc _mode _cart _env Nothing _holeMap sd = pure sd
applyBinder doc mode cart env (Just binder) holeMap sd =
  case binder of
    BinderInfo _ (BinderInput varName tyAnn) -> do
      tyAnn' <- liftEither (elabSurfaceTypeExpr doc mode tyAnn)
      let varTy = applySubstTy (eeTypeSubst env) tyAnn'
      let (source, diag1) = freshPort varTy (sdDiag sd)
      let sd1 = sd { sdDiag = diag1 }
      sd2 <- connectVar doc mode cart varName source varTy sd1 True
      pure sd2
    BinderInfo _ (BinderValue varName valueArgIdx) -> do
      let holeIdx = M.lookup valueArgIdx holeMap
      case holeIdx of
        Nothing -> liftEither (Left "surface: missing bound value")
        Just hidx -> do
          let ports = M.findWithDefault [] (TagHole hidx) (sdTags sd)
          case ports of
            [source] -> do
              let tySource = diagramPortType (sdDiag sd) source
              ty <- case tySource of
                Nothing -> liftEither (Left "surface: missing bound value type")
                Just t -> pure t
              sd1 <- unifyVarType varName ty sd
              sd2 <- connectVar doc mode cart varName source ty sd1 False
              let tags' = M.delete (TagHole hidx) (sdTags sd2)
              pure sd2 { sdTags = tags' }
            _ ->
              let count = length ports
              in liftEither (Left ("surface: bound value must have exactly one output (" <> T.pack (show count) <> ")"))

unifyVarType :: Text -> TypeExpr -> SurfDiag -> Fresh SurfDiag
unifyVarType varName ty sd =
  case M.lookup varName (sdUses sd) of
    Nothing -> pure sd
    Just [] -> pure sd
    Just (p:_) ->
      case diagramPortType (sdDiag sd) p of
        Nothing -> pure sd
        Just tyUse -> do
          let flex = S.union (freeTyVars tyUse) (freeTyVars ty)
          subst <- liftEither (unifyTyFlex flex tyUse ty)
          pure (applySubstSurf subst sd)
  where
    freeTyVars = varsInTy
    varsInTy t =
      case t of
        Ty.TVar v -> S.singleton v
        Ty.TCon _ xs -> S.unions (map varsInTy xs)

connectVar :: Doctrine -> ModeName -> StructuralOps -> Text -> PortId -> TypeExpr -> SurfDiag -> Bool -> Fresh SurfDiag
connectVar _doc _mode ops varName source ty sd sourceIsInput = do
  let uses = M.findWithDefault [] varName (sdUses sd)
  let useInOutput = any (`elem` dOut (sdDiag sd)) uses
  sd1 <- connectUses ops varName source ty uses sd
  let diag1 = sdDiag sd1
  let dIn' = if sourceIsInput then ensureIn source (dIn diag1) else dIn diag1
  let dOut' =
        if sourceIsInput
          then dOut diag1
          else if useInOutput
            then dOut diag1
            else removePort source (dOut diag1)
  let diag2 = diag1 { dIn = dIn', dOut = dOut' }
  pure sd1 { sdDiag = diag2, sdUses = M.delete varName (sdUses sd1) }
  where
    ensureIn p xs = if p `elem` xs then xs else p:xs
    removePort p = filter (/= p)

connectUses :: StructuralOps -> Text -> PortId -> TypeExpr -> [PortId] -> SurfDiag -> Fresh SurfDiag
connectUses ops varName source ty uses sd =
  case uses of
    [] -> do
      case (soDiscipline ops, soDrop ops) of
        (Affine, Just dropGen) -> addDrop dropGen
        (Cartesian, Just dropGen) -> addDrop dropGen
        (disc, _) ->
          liftEither
            (Left ("surface: variable " <> varName <> " dropped (uses 0) under " <> renderDiscipline disc))
    [p] -> do
      (diag1, uses1, tags1) <- mergePortsAll source p sd
      pure sd { sdDiag = diag1, sdUses = uses1, sdTags = tags1 }
    _ -> do
      case (soDiscipline ops, soDup ops) of
        (Relevant, Just dupGen) -> addDup dupGen
        (Cartesian, Just dupGen) -> addDup dupGen
        (disc, _) ->
          liftEither
            (Left ("surface: variable " <> varName <> " duplicated (uses " <> T.pack (show (length uses)) <> ") under " <> renderDiscipline disc))
  where
    addDrop dropGen = do
      liftEither (ensureStructuralGenAttrs dropGen)
      let diag0 = sdDiag sd
      diag1 <- liftEither (addEdgePayload (PGen (gdName dropGen) M.empty) [source] [] diag0)
      pure sd { sdDiag = diag1 }
    addDup dupGen = do
      liftEither (ensureStructuralGenAttrs dupGen)
      (outs, diag1) <- dupOutputs dupGen source ty (sdDiag sd) (length uses)
      let sd1 = sd { sdDiag = diag1 }
      foldM mergeOne sd1 (zip outs uses)
    renderDiscipline disc =
      case disc of
        Linear -> "linear discipline"
        Affine -> "affine discipline"
        Relevant -> "relevant discipline"
        Cartesian -> "cartesian discipline"
    mergeOne acc (outP, useP) = do
      (diag1, uses1, tags1) <- mergePortsAll outP useP acc
      let diag2 = diag1 { dIn = filter (/= outP) (dIn diag1) }
      pure acc { sdDiag = diag2, sdUses = uses1, sdTags = tags1 }

mergePortsAll :: PortId -> PortId -> SurfDiag -> Fresh (Diagram, Uses, Tags)
mergePortsAll keep drop sd = do
  diag' <- liftEither (mergePorts (sdDiag sd) keep drop)
  let uses' = replacePortUses keep drop (sdUses sd)
  let tags' = replacePortTags keep drop (sdTags sd)
  pure (diag', uses', tags')


-- Duplication tree

dupOutputs :: GenDecl -> PortId -> TypeExpr -> Diagram -> Int -> Fresh ([PortId], Diagram)
dupOutputs dupGen source ty diag n
  | not (null (gdAttrs dupGen)) = liftEither (Left "surface: structural generator dup/drop must not declare attributes")
  | n <= 0 = pure ([], diag)
  | n == 1 = pure ([source], diag)
  | otherwise = do
      let (p1, diag1) = freshPort ty diag
      let (p2, diag2) = freshPort ty diag1
      diag3 <- liftEither (addEdgePayload (PGen (gdName dupGen) M.empty) [source] [p1, p2] diag2)
      (rest, diag4) <- dupOutputs dupGen p2 ty diag3 (n - 1)
      pure (p1:rest, diag4)

ensureStructuralGenAttrs :: GenDecl -> Either Text ()
ensureStructuralGenAttrs gen =
  if null (gdAttrs gen)
    then Right ()
    else Left "surface: structural generator dup/drop must not declare attributes"


-- Template helpers

tagHole :: Int -> SurfDiag -> SurfDiag
tagHole n sd =
  let tag = TagHole n
      ports = dOut (sdDiag sd)
      tags' = M.insertWith (<>) tag ports (sdTags sd)
  in sd { sdTags = tags' }

varSurf :: ModeName -> Text -> TypeExpr -> SurfDiag
varSurf mode name ty =
  let diag = idD mode [ty]
  in SurfDiag diag (M.singleton name (dIn diag)) M.empty


-- Diagram construction helpers

lookupGen :: Doctrine -> ModeName -> GenName -> Either Text GenDecl
lookupGen doc mode name =
  case M.lookup mode (dGens doc) >>= M.lookup name of
    Nothing -> Left "surface: unknown generator"
    Just gd -> Right gd

genDFromDecl :: ModeName -> ElabEnv -> GenDecl -> Maybe [TypeExpr] -> AttrMap -> Fresh Diagram
genDFromDecl mode env gen mArgs attrs = do
  let tyVars = gdTyVars gen
  let subst0 = eeTypeSubst env
  renameSubst <- freshSubst tyVars
  let dom0 = applySubstCtx renameSubst (gdDom gen)
  let cod0 = applySubstCtx renameSubst (gdCod gen)
  let (dom1, cod1) = (applySubstCtx subst0 dom0, applySubstCtx subst0 cod0)
  (dom, cod) <- case mArgs of
    Nothing -> pure (dom1, cod1)
    Just args -> do
      let args' = map (applySubstTy subst0) args
      if length args' /= length tyVars
        then liftEither (Left "surface: generator type argument mismatch")
        else do
          freshVars <- liftEither (extractFreshVars tyVars renameSubst)
          let subst = M.fromList (zip freshVars args')
          pure (applySubstCtx subst dom1, applySubstCtx subst cod1)
  liftEither (buildGenDiagram mode dom cod (gdName gen) attrs)

buildGenDiagram :: ModeName -> Context -> Context -> GenName -> AttrMap -> Either Text Diagram
buildGenDiagram mode dom cod gen attrs = do
  let (inPorts, diag1) = allocPorts dom (emptyDiagram mode)
  let (outPorts, diag2) = allocPorts cod diag1
  diag3 <- addEdgePayload (PGen gen attrs) inPorts outPorts diag2
  let diagFinal = diag3 { dIn = inPorts, dOut = outPorts }
  validateDiagram diagFinal
  pure diagFinal

allocPorts :: Context -> Diagram -> ([PortId], Diagram)
allocPorts [] diag = ([], diag)
allocPorts (ty:rest) diag =
  let (pid, diag1) = freshPort ty diag
      (pids, diag2) = allocPorts rest diag1
  in (pid:pids, diag2)

-- Composition with tags and uses

compSurf :: SurfDiag -> SurfDiag -> Either Text SurfDiag
compSurf a b = do
  codA <- diagramCod (sdDiag a)
  domB <- diagramDom (sdDiag b)
  let flex = S.union (freeTyVarsDiagram (sdDiag a)) (freeTyVarsDiagram (sdDiag b))
  subst <- unifyCtxFlex flex codA domB
  let a' = applySubstSurf subst a
  let b' = applySubstSurf subst b
  let bShift = shiftDiagram (dNextPort (sdDiag a')) (dNextEdge (sdDiag a')) (sdDiag b')
  let usesShift = shiftUses (dNextPort (sdDiag a')) (sdUses b')
  let tagsShift = shiftTags (dNextPort (sdDiag a')) (sdTags b')
  merged <- unionDiagram (sdDiag a') bShift
  let merged0 = merged { dIn = dIn (sdDiag a'), dOut = dOut bShift }
  (diagFinal, usesFinal, tagsFinal) <- foldM mergeStep (merged0, mergeUses (sdUses a') usesShift, mergeTags (sdTags a') tagsShift) (zip (dOut (sdDiag a')) (dIn bShift))
  pure SurfDiag { sdDiag = diagFinal, sdUses = usesFinal, sdTags = tagsFinal }
  where
    mergeStep (d, u, t) (pOut, pIn) = do
      d' <- mergePorts d pOut pIn
      let u' = replacePortUses pOut pIn u
      let t' = replacePortTags pOut pIn t
      pure (d', u', t')

tensorSurf :: SurfDiag -> SurfDiag -> Either Text SurfDiag
tensorSurf a b = do
  let bShift = shiftDiagram (dNextPort (sdDiag a)) (dNextEdge (sdDiag a)) (sdDiag b)
  merged <- unionDiagram (sdDiag a) bShift
  let usesShift = shiftUses (dNextPort (sdDiag a)) (sdUses b)
  let tagsShift = shiftTags (dNextPort (sdDiag a)) (sdTags b)
  let diagFinal = merged { dIn = dIn (sdDiag a) <> dIn bShift, dOut = dOut (sdDiag a) <> dOut bShift }
  pure SurfDiag
    { sdDiag = diagFinal
    , sdUses = mergeUses (sdUses a) usesShift
    , sdTags = mergeTags (sdTags a) tagsShift
    }

unionDiagram :: Diagram -> Diagram -> Either Text Diagram
unionDiagram left right = do
  portTy <- unionDisjointIntMap "unionDiagram ports" (dPortTy left) (dPortTy right)
  prod <- unionDisjointIntMap "unionDiagram producers" (dProd left) (dProd right)
  cons <- unionDisjointIntMap "unionDiagram consumers" (dCons left) (dCons right)
  edges <- unionDisjointIntMap "unionDiagram edges" (dEdges left) (dEdges right)
  pure left
    { dPortTy = portTy
    , dProd = prod
    , dCons = cons
    , dEdges = edges
    , dNextPort = dNextPort right
    , dNextEdge = dNextEdge right
    }

boxSurf :: ModeName -> Text -> SurfDiag -> Either Text SurfDiag
boxSurf mode name inner = do
  dom <- diagramDom (sdDiag inner)
  cod <- diagramCod (sdDiag inner)
  let (ins, diag0) = allocPorts dom (emptyDiagram mode)
  let (outs, diag1) = allocPorts cod diag0
  diag2 <- addEdgePayload (PBox (BoxName name) (sdDiag inner)) ins outs diag1
  let diag3 = diag2 { dIn = ins, dOut = outs }
  validateDiagram diag3
  uses' <- remapUses (sdDiag inner) ins outs (sdUses inner)
  tags' <- remapTags (sdDiag inner) ins outs (sdTags inner)
  pure SurfDiag { sdDiag = diag3, sdUses = uses', sdTags = tags' }

loopSurf :: SurfDiag -> Either Text SurfDiag
loopSurf sd =
  case (dIn (sdDiag sd), dOut (sdDiag sd)) of
    ([pIn], pOut:pOuts) -> do
      diag1 <- mergePorts (sdDiag sd) pOut pIn
      let uses' = replacePortUses pOut pIn (sdUses sd)
      let tags' = replacePortTags pOut pIn (sdTags sd)
      let diag2 = diag1 { dIn = [], dOut = pOuts }
      validateDiagram diag2
      pure sd { sdDiag = diag2, sdUses = uses', sdTags = tags' }
    _ -> Left "loop: expected exactly one input and at least one output"

remapUses :: Diagram -> [PortId] -> [PortId] -> Uses -> Either Text Uses
remapUses inner outerIns outerOuts uses = do
  let innerIns = dIn inner
  let innerOuts = dOut inner
  let mapping = M.fromList (zip innerIns outerIns) <> M.fromList (zip innerOuts outerOuts)
  let remapPort p =
        case M.lookup p mapping of
          Just q -> Right q
          Nothing -> Left "surface: boxed variable not on boundary"
  let remapList ps = mapM remapPort ps
  mapM remapList uses

remapTags :: Diagram -> [PortId] -> [PortId] -> Tags -> Either Text Tags
remapTags inner outerIns outerOuts tags = do
  let innerIns = dIn inner
  let innerOuts = dOut inner
  let mapping = M.fromList (zip innerIns outerIns) <> M.fromList (zip innerOuts outerOuts)
  let remapPort p =
        case M.lookup p mapping of
          Just q -> Right q
          Nothing -> Left "surface: boxed tag not on boundary"
  let remapList ps = mapM remapPort ps
  mapM remapList tags


-- Fresh monad

newtype Fresh a = Fresh { runFresh :: Int -> Either Text (a, Int) }

instance Functor Fresh where
  fmap f (Fresh g) =
    Fresh (\n -> do
      (a, n') <- g n
      pure (f a, n'))

instance Applicative Fresh where
  pure a = Fresh (\n -> Right (a, n))
  Fresh f <*> Fresh g =
    Fresh (\n -> do
      (h, n1) <- f n
      (a, n2) <- g n1
      pure (h a, n2))

instance Monad Fresh where
  Fresh g >>= k =
    Fresh (\n -> do
      (a, n1) <- g n
      let Fresh h = k a
      h n1)

evalFresh :: Fresh a -> Either Text a
evalFresh (Fresh f) = fmap fst (f 0)

freshSubst :: [TyVar] -> Fresh Subst
freshSubst vars = do
  pairs <- mapM freshVar vars
  pure (M.fromList pairs)

extractFreshVars :: [TyVar] -> Subst -> Either Text [TyVar]
extractFreshVars vars subst =
  mapM lookupVar vars
  where
    lookupVar v =
      case M.lookup v subst of
        Just (Ty.TVar v') -> Right v'
        _ -> Left "internal error: expected fresh type variable"

freshVar :: TyVar -> Fresh (TyVar, TypeExpr)
freshVar v = do
  n <- freshInt
  let name = tvName v <> T.pack ("#" <> show n)
  let fresh = v { tvName = name }
  pure (v, Ty.TVar fresh)

freshTyVar :: TyVar -> Fresh TyVar
freshTyVar v = do
  n <- freshInt
  let name = tvName v <> T.pack ("#" <> show n)
  pure v { tvName = name }

freshInt :: Fresh Int
freshInt = Fresh (\n -> Right (n, n + 1))

liftEither :: Either Text a -> Fresh a
liftEither (Left err) = Fresh (\_ -> Left err)
liftEither (Right a) = pure a
