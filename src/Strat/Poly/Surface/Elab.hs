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
import Strat.Poly.Doctrine (Doctrine(..), GenDecl(..))
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.Names (GenName(..), BoxName(..))
import Strat.Poly.TypeExpr (TypeExpr, TypeName(..), TyVar(..), Context)
import qualified Strat.Poly.TypeExpr as Ty
import Strat.Poly.UnifyTy (Subst, applySubstTy, applySubstCtx, unifyTyFlex, composeSubst)
import Strat.Poly.Diagram (Diagram(..), idD, diagramDom, diagramCod, freeTyVarsDiagram, applySubstDiagram)
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


-- Public entrypoint

elabSurfaceExpr :: Doctrine -> PolySurfaceDef -> Text -> Either Text Diagram
elabSurfaceExpr doc surf src = do
  let spec = psSpec surf
  ast <- parseSurfaceExpr spec src
  cart <- requireCartesian doc (psMode surf)
  let env0 = initEnv spec
  diag <- evalFresh (elabAst doc (psMode surf) spec cart env0 ast)
  if M.null (sdUses diag)
    then validateDiagram (sdDiag diag) >> pure (sdDiag diag)
    else Left "surface: unresolved variables"


-- Elaboration environment

data ElabEnv = ElabEnv
  { eeVars :: M.Map Text TypeExpr
  , eeVarDefs :: M.Map Text Diagram
  , eeTypeSubst :: Subst
  , eeCtxVar :: Maybe TyVar
  } deriving (Eq, Show)

initEnv :: SurfaceSpec -> ElabEnv
initEnv spec =
  case ssContext spec of
    Nothing -> ElabEnv M.empty M.empty M.empty Nothing
    Just (ctxName, ty) ->
      ElabEnv M.empty M.empty (M.singleton (TyVar ctxName) ty) (Just (TyVar ctxName))


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
applySubstSurf subst sd = sd { sdDiag = applySubstDiagram subst (sdDiag sd) }

unifyCtxFlex :: S.Set TyVar -> Context -> Context -> Either Text Subst
unifyCtxFlex flex ctx1 ctx2
  | length ctx1 /= length ctx2 = Left "surface: context length mismatch"
  | otherwise = foldl step (Right M.empty) (zip ctx1 ctx2)
  where
    step acc (a, b) = do
      s <- acc
      s' <- unifyTyFlex flex (applySubstTy s a) (applySubstTy s b)
      pure (composeSubst s' s)


-- Cartesian structure

data CartesianOps = CartesianOps
  { coDup :: GenDecl
  , coDrop :: GenDecl
  } deriving (Eq, Show)

requireCartesian :: Doctrine -> ModeName -> Either Text CartesianOps
requireCartesian doc mode = do
  dup <- requireGen doc mode "dup"
  dropGen <- requireGen doc mode "drop"
  ensureDupShape dup
  ensureDropShape dropGen
  pure CartesianOps { coDup = dup, coDrop = dropGen }

requireGen :: Doctrine -> ModeName -> Text -> Either Text GenDecl
requireGen doc mode name =
  case M.lookup mode (dGens doc) >>= M.lookup (GenName name) of
    Nothing -> Left ("surface: missing generator " <> name)
    Just gen -> Right gen

ensureDupShape :: GenDecl -> Either Text ()
ensureDupShape gen =
  case (gdTyVars gen, gdDom gen, gdCod gen) of
    ([v], [Ty.TVar v1], [Ty.TVar v2, Ty.TVar v3])
      | v == v1 && v == v2 && v == v3 -> Right ()
    _ -> Left "surface: dup has wrong type"

ensureDropShape :: GenDecl -> Either Text ()
ensureDropShape gen =
  case (gdTyVars gen, gdDom gen, gdCod gen) of
    ([v], [Ty.TVar v1], []) | v == v1 -> Right ()
    _ -> Left "surface: drop has wrong type"



-- Elaboration core

elabAst :: Doctrine -> ModeName -> SurfaceSpec -> CartesianOps -> ElabEnv -> SurfaceAST -> Fresh SurfDiag
elabAst doc mode spec cart env ast =
  case ast of
    SAIdent name ->
      case M.lookup name (eeVars env) of
        Just ty -> elabVarRef doc mode env (eeTypeSubst env) name ty
        Nothing -> elabZeroArgGen doc mode env name
    SAType _ -> liftEither (Left "surface: unexpected type where expression expected")
    SANode ctor args ->
      if ctor == "CALL"
        then elabCall doc mode spec cart env args
        else do
          rule <- case M.lookup ctor (ssElabRules spec) of
            Nothing -> liftEither (Left ("surface: missing elaboration rule for " <> ctor))
            Just r -> pure r
          elabNode doc mode spec cart env rule args

elabZeroArgGen :: Doctrine -> ModeName -> ElabEnv -> Text -> Fresh SurfDiag
elabZeroArgGen doc mode env name = do
  gen <- liftEither (lookupGen doc mode (GenName name))
  if null (gdDom gen)
    then do
      diag <- genDFromDecl mode env gen Nothing
      pure (emptySurf diag)
    else liftEither (Left ("surface: unknown variable " <> name))

elabCall :: Doctrine -> ModeName -> SurfaceSpec -> CartesianOps -> ElabEnv -> [SurfaceAST] -> Fresh SurfDiag
elabCall doc mode _spec _cart env args =
  case args of
    [SAIdent name, argExpr] -> do
      argDiag <- elabAst doc mode _spec _cart env argExpr
      gen <- liftEither (lookupGen doc mode (GenName name))
      buildGenCall doc mode env gen argDiag
    _ -> liftEither (Left "surface: CALL expects name and argument expression")

buildGenCall :: Doctrine -> ModeName -> ElabEnv -> GenDecl -> SurfDiag -> Fresh SurfDiag
buildGenCall _doc mode env gen argDiag = do
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
  diag2 <- liftEither (addEdgePayload (PGen (gdName gen)) argPorts outPorts diag1)
  let diag3 = diag2 { dOut = outPorts }
  liftEither (validateDiagram diag3)
  pure argDiag' { sdDiag = diag3 }
  where
    freeTyVarsCtx = S.unions . map freeTyVarsTy
    freeTyVarsTy ty =
      case ty of
        Ty.TVar v -> S.singleton v
        Ty.TCon _ xs -> S.unions (map freeTyVarsTy xs)

elabNode :: Doctrine -> ModeName -> SurfaceSpec -> CartesianOps -> ElabEnv -> ElabRule -> [SurfaceAST] -> Fresh SurfDiag
elabNode doc mode spec cart env rule args = do
  let params = erArgs rule
  if length params /= length args
    then liftEither (Left "surface: elaboration rule arity mismatch")
    else do
      let paramMap = M.fromList (zip params args)
      let typeSubst = buildTypeSubst env paramMap
      let (binder, bodyIndex, exprInfos) = detectBinder params args
      (childDiags, holeMap) <- elabChildren doc mode spec cart env binder bodyIndex exprInfos
      let childList = map snd childDiags
      surf <- evalTemplate doc mode spec cart env paramMap typeSubst holeMap childList (erTemplate rule)
      surf' <- applyBinder doc mode cart env binder holeMap surf
      pure surf'


-- Detect binder information

data BinderKind
  = BinderInput Text TypeExpr
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

elabChildren :: Doctrine -> ModeName -> SurfaceSpec -> CartesianOps -> ElabEnv -> Maybe BinderInfo -> Maybe Int -> [(Int, SurfaceAST)] -> Fresh ([(Int, SurfDiag)], HoleMap)
elabChildren doc mode spec cart env binder bodyIndex exprInfos = do
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
      d <- elabAst doc mode spec cart env' expr
      pure (idx, d)

extendEnv :: Doctrine -> ModeName -> ElabEnv -> BinderInfo -> Fresh ElabEnv
extendEnv doc mode env (BinderInfo _ (BinderInput varName tyAnn)) = do
  let ty0 = applySubstTy (eeTypeSubst env) tyAnn
  case lookupCtxVar env of
    Nothing ->
      pure env
        { eeVars = M.insert varName ty0 (eeVars env)
        , eeVarDefs = M.delete varName (eeVarDefs env)
        }
    Just (ctxVar, ctxTy) -> do
      let newCtx = Ty.TCon (TypeName "prod") [ctxTy, ty0]
      let varTy = Ty.TCon (TypeName "Hom") [newCtx, ty0]
      exrDecl <- liftEither (requireExr doc mode)
      exrDiag <- genDFromDecl mode env exrDecl (Just [ctxTy, ty0])
      let subst' = M.insert ctxVar newCtx (eeTypeSubst env)
      pure env
        { eeVars = M.insert varName varTy (eeVars env)
        , eeVarDefs = M.insert varName exrDiag (eeVarDefs env)
        , eeTypeSubst = subst'
        }
extendEnv _doc _mode env (BinderInfo _ (BinderValue varName _)) = do
  fresh <- freshTyVar (TyVar varName)
  let ty = Ty.TVar fresh
  pure env
    { eeVars = M.insert varName ty (eeVars env)
    , eeVarDefs = M.delete varName (eeVarDefs env)
    }

lookupCtxVar :: ElabEnv -> Maybe (TyVar, TypeExpr)
lookupCtxVar env =
  case eeCtxVar env of
    Nothing -> Nothing
    Just v -> do
      ty <- M.lookup v (eeTypeSubst env)
      pure (v, ty)

computeInputVarType :: ElabEnv -> TypeExpr -> (TypeExpr, Maybe (TyVar, TypeExpr))
computeInputVarType env tyAnn =
  let ty0 = applySubstTy (eeTypeSubst env) tyAnn
  in case lookupCtxVar env of
    Nothing -> (ty0, Nothing)
    Just (ctxVar, ctxTy) ->
      let newCtx = Ty.TCon (TypeName "prod") [ctxTy, ty0]
          varTy = Ty.TCon (TypeName "Hom") [newCtx, ty0]
      in (varTy, Just (ctxVar, newCtx))


data ProdStep = ProdStep
  { psCur :: TypeExpr
  , psLeft :: TypeExpr
  , psRight :: TypeExpr
  } deriving (Eq, Show)

splitHom :: TypeExpr -> Maybe (TypeExpr, TypeExpr)
splitHom ty =
  case ty of
    Ty.TCon (TypeName "Hom") [dom, cod] -> Just (dom, cod)
    _ -> Nothing

splitProd :: TypeExpr -> Maybe (TypeExpr, TypeExpr)
splitProd ty =
  case ty of
    Ty.TCon (TypeName "prod") [l, r] -> Just (l, r)
    _ -> Nothing

prodPeelSteps :: TypeExpr -> TypeExpr -> Either Text [ProdStep]
prodPeelSteps ctxCur dom = go ctxCur []
  where
    go cur acc
      | cur == dom = Right (reverse acc)
      | otherwise =
          case splitProd cur of
            Just (l, r) -> go l (ProdStep cur l r : acc)
            Nothing ->
              Left ("surface: cannot weaken from ctx " <> T.pack (show ctxCur) <> " to " <> T.pack (show dom))

requireCtxThreadOps :: Doctrine -> ModeName -> Either Text (GenDecl, GenDecl)
requireCtxThreadOps doc mode = do
  exl <- requireGen doc mode "exl"
  comp <- requireGen doc mode "comp"
  ensureExlShape exl
  ensureCompShape comp
  pure (exl, comp)

ensureExlShape :: GenDecl -> Either Text ()
ensureExlShape gen =
  case (gdTyVars gen, gdDom gen, gdCod gen) of
    ([a, b], [], [Ty.TCon (TypeName "Hom") [Ty.TCon (TypeName "prod") [Ty.TVar a1, Ty.TVar b1], Ty.TVar a2]])
      | a == a1 && a == a2 && b == b1 -> Right ()
    _ -> Left "surface: exl has wrong type"

requireExr :: Doctrine -> ModeName -> Either Text GenDecl
requireExr doc mode = do
  exr <- requireGen doc mode "exr"
  ensureExrShape exr
  pure exr

ensureExrShape :: GenDecl -> Either Text ()
ensureExrShape gen =
  case (gdTyVars gen, gdDom gen, gdCod gen) of
    ([a, b], [], [Ty.TCon (TypeName "Hom") [Ty.TCon (TypeName "prod") [Ty.TVar a1, Ty.TVar b1], Ty.TVar b2]])
      | a == a1 && b == b1 && b == b2 -> Right ()
    _ -> Left "surface: exr has wrong type"

ensureCompShape :: GenDecl -> Either Text ()
ensureCompShape gen =
  case (gdTyVars gen, gdDom gen, gdCod gen) of
    ( [a, b, c]
      , [ Ty.TCon (TypeName "Hom") [Ty.TVar b1, Ty.TVar c1]
        , Ty.TCon (TypeName "Hom") [Ty.TVar a1, Ty.TVar b2]
        ]
      , [Ty.TCon (TypeName "Hom") [Ty.TVar a2, Ty.TVar c2]]
      )
      | a == a1 && a == a2 && b == b1 && b == b2 && c == c1 && c == c2 -> Right ()
    _ -> Left "surface: comp has wrong type"

elabVarRef :: Doctrine -> ModeName -> ElabEnv -> Subst -> Text -> TypeExpr -> Fresh SurfDiag
elabVarRef doc mode env subst name ty = do
  let ty' = applySubstTy subst ty
  let base0 =
        case M.lookup name (eeVarDefs env) of
          Just def -> emptySurf def
          Nothing -> varSurf mode name ty'
  let base = applySubstSurf subst base0
  case lookupCtxVar env of
    Nothing -> pure base
    Just (_ctxVar, ctxTy0) -> do
      let ctxTy = applySubstTy subst ctxTy0
      case splitHom ty' of
        Nothing -> pure base
        Just (dom, cod) ->
          if ctxTy == dom
            then pure base
            else do
              (exlDecl, compDecl) <- liftEither (requireCtxThreadOps doc mode)
              steps <- liftEither (prodPeelSteps ctxTy dom)
              proj <- buildProjection doc mode env exlDecl compDecl ctxTy steps
              applyWeakeningVal mode env compDecl dom cod ctxTy base proj

buildProjection :: Doctrine -> ModeName -> ElabEnv -> GenDecl -> GenDecl -> TypeExpr -> [ProdStep] -> Fresh SurfDiag
buildProjection _doc mode env exlDecl compDecl ctxCur steps =
  case steps of
    [] -> liftEither (Left "surface: empty projection steps")
    (step0:rest) -> do
      acc <- exlDiag step0
      foldM (composeStep ctxCur) acc rest
  where
    exlDiag step = do
      diag <- genDFromDecl mode env exlDecl (Just [psLeft step, psRight step])
      pure (emptySurf diag)
    composeStep ctxRoot acc step = do
      exl <- exlDiag step
      compDiag <- genDFromDecl mode env compDecl (Just [ctxRoot, psCur step, psLeft step])
      let compSurfDiag = emptySurf compDiag
      liftEither (tensorSurf exl acc >>= \t -> compSurf t compSurfDiag)

applyWeakeningVal :: ModeName -> ElabEnv -> GenDecl -> TypeExpr -> TypeExpr -> TypeExpr -> SurfDiag -> SurfDiag -> Fresh SurfDiag
applyWeakeningVal mode env compDecl dom cod ctxCur base proj = do
  compDiag <- genDFromDecl mode env compDecl (Just [ctxCur, dom, cod])
  let compSurfDiag = emptySurf compDiag
  liftEither (tensorSurf base proj >>= \t -> compSurf t compSurfDiag)


-- Template evaluation

evalTemplate :: Doctrine -> ModeName -> SurfaceSpec -> CartesianOps -> ElabEnv -> M.Map Text SurfaceAST -> Subst -> HoleMap -> [SurfDiag] -> TemplateExpr -> Fresh SurfDiag
evalTemplate doc mode _spec _cart env paramMap subst holeMap childList templ =
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
    TId ctx -> do
      let ctx' = map (applySubstTy subst) ctx
      pure (emptySurf (idD mode ctx'))
    TGen name mArgs -> do
      gen <- liftEither (lookupGen doc mode (GenName name))
      let args' = fmap (map (applySubstTy subst)) mArgs
      diag <- genDFromDecl mode env gen args'
      pure (emptySurf diag)
    TBox name inner -> do
      innerDiag <- evalTemplate doc mode _spec _cart env paramMap subst holeMap childList inner
      liftEither (boxSurf mode name innerDiag)
    TLoop inner -> do
      innerDiag <- evalTemplate doc mode _spec _cart env paramMap subst holeMap childList inner
      liftEither (loopSurf innerDiag)
    TComp a b -> do
      d1 <- evalTemplate doc mode _spec _cart env paramMap subst holeMap childList a
      d2 <- evalTemplate doc mode _spec _cart env paramMap subst holeMap childList b
      liftEither (compSurf d1 d2)
    TTensor a b -> do
      d1 <- evalTemplate doc mode _spec _cart env paramMap subst holeMap childList a
      d2 <- evalTemplate doc mode _spec _cart env paramMap subst holeMap childList b
      liftEither (tensorSurf d1 d2)

buildTypeSubst :: ElabEnv -> M.Map Text SurfaceAST -> Subst
buildTypeSubst env paramMap =
  let local = M.fromList
        [ (TyVar name, ty)
        | (name, SAType ty) <- M.toList paramMap
        ]
  in M.union local (eeTypeSubst env)


-- Apply binder after template evaluation

applyBinder :: Doctrine -> ModeName -> CartesianOps -> ElabEnv -> Maybe BinderInfo -> HoleMap -> SurfDiag -> Fresh SurfDiag
applyBinder _doc _mode _cart _env Nothing _holeMap sd = pure sd
applyBinder doc mode cart env (Just binder) holeMap sd =
  case binder of
    BinderInfo _ (BinderInput varName tyAnn) ->
      case lookupCtxVar env of
        Just _ -> pure sd
        Nothing -> do
          let (varTy, _mCtx) = computeInputVarType env tyAnn
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

connectVar :: Doctrine -> ModeName -> CartesianOps -> Text -> PortId -> TypeExpr -> SurfDiag -> Bool -> Fresh SurfDiag
connectVar _doc _mode cart varName source ty sd sourceIsInput = do
  let uses = M.findWithDefault [] varName (sdUses sd)
  let useInOutput = any (`elem` dOut (sdDiag sd)) uses
  sd1 <- connectUses cart source ty uses sd
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

connectUses :: CartesianOps -> PortId -> TypeExpr -> [PortId] -> SurfDiag -> Fresh SurfDiag
connectUses cart source ty uses sd =
  case uses of
    [] -> do
      let diag0 = sdDiag sd
      diag1 <- liftEither (addEdgePayload (PGen (gdName (coDrop cart))) [source] [] diag0)
      pure sd { sdDiag = diag1 }
    [p] -> do
      (diag1, uses1, tags1) <- mergePortsAll source p sd
      pure sd { sdDiag = diag1, sdUses = uses1, sdTags = tags1 }
    _ -> do
      (outs, diag1) <- dupOutputs (coDup cart) source ty (sdDiag sd) (length uses)
      let sd1 = sd { sdDiag = diag1 }
      foldM mergeOne sd1 (zip outs uses)
  where
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
  | n <= 0 = pure ([], diag)
  | n == 1 = pure ([source], diag)
  | otherwise = do
      let (p1, diag1) = freshPort ty diag
      let (p2, diag2) = freshPort ty diag1
      diag3 <- liftEither (addEdgePayload (PGen (gdName dupGen)) [source] [p1, p2] diag2)
      (rest, diag4) <- dupOutputs dupGen p2 ty diag3 (n - 1)
      pure (p1:rest, diag4)


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

genDFromDecl :: ModeName -> ElabEnv -> GenDecl -> Maybe [TypeExpr] -> Fresh Diagram
genDFromDecl mode env gen mArgs = do
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
  liftEither (buildGenDiagram mode dom cod (gdName gen))

buildGenDiagram :: ModeName -> Context -> Context -> GenName -> Either Text Diagram
buildGenDiagram mode dom cod gen = do
  let (inPorts, diag1) = allocPorts dom (emptyDiagram mode)
  let (outPorts, diag2) = allocPorts cod diag1
  diag3 <- addEdgePayload (PGen gen) inPorts outPorts diag2
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
freshVar (TyVar base) = do
  n <- freshInt
  let name = base <> T.pack ("#" <> show n)
  pure (TyVar base, Ty.TVar (TyVar name))

freshTyVar :: TyVar -> Fresh TyVar
freshTyVar (TyVar base) = do
  n <- freshInt
  pure (TyVar (base <> T.pack ("#" <> show n)))

freshInt :: Fresh Int
freshInt = Fresh (\n -> Right (n, n + 1))

liftEither :: Either Text a -> Fresh a
liftEither (Left err) = Fresh (\_ -> Left err)
liftEither (Right a) = pure a
