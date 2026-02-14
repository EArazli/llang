{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Surface.Elab
  ( elabSurfaceExpr
  ) where

import Control.Monad (foldM)
import qualified Data.IntMap.Strict as IM
import Data.List (sort)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import Strat.Common.Rules (RewritePolicy(..))
import Strat.Frontend.Env (ModuleEnv(..), TermDef(..))
import Strat.Poly.Attr
import Strat.Poly.Doctrine (Doctrine(..), GenDecl(..), TypeSig(..), ParamSig(..), InputShape(..), BinderSig(..), lookupTypeSig, gdPlainDom, doctrineTypeTheory)
import Strat.Poly.DSL.AST (RawPolyTypeExpr(..), RawTypeRef(..), RawModExpr(..))
import Strat.Poly.Diagram (Diagram(..), idD, genD, unionDiagram, diagramDom, diagramCod, freeTyVarsDiagram, freeAttrVarsDiagram, applySubstDiagram)
import Strat.Poly.Graph
  ( PortId(..)
  , Edge(..)
  , BinderMetaVar(..)
  , BinderArg(..)
  , EdgePayload(..)
  , ePayload
  , emptyDiagram
  , freshPort
  , addEdgePayload
  , mergePorts
  , setPortLabel
  , validateDiagram
  , shiftDiagram
  , diagramPortType
  )
import Strat.Poly.ModeTheory (ModeName(..), ModeTheory(..), ModName(..), ModDecl(..), ModExpr(..))
import Strat.Poly.Names (GenName(..), BoxName(..))
import Strat.Poly.Normalize (NormalizationStatus(..), normalize)
import Strat.Poly.Rewrite (RewriteRule(..), rulesFromPolicy)
import Strat.Poly.Surface.Parse (SurfaceNode(..), SurfaceParam(..), parseSurfaceExpr)
import Strat.Poly.Surface.Spec
import Strat.Poly.TypeExpr (TypeExpr, TypeName(..), TypeRef(..), TyVar(..), Context, typeMode, freeTyVarsType)
import qualified Strat.Poly.TypeExpr as Ty
import Strat.Poly.TypeTheory (TypeTheory, modeOnlyTypeTheory)
import qualified Strat.Poly.UnifyTy as U
import qualified Strat.Poly.Morphism as PolyMorph
import Strat.Util.List (dedupe)


type Subst = U.Subst

applySubstTy :: ModeTheory -> Subst -> TypeExpr -> Either Text TypeExpr
applySubstTy mt =
  U.applySubstTy (modeOnlyTypeTheory mt)

applySubstCtx :: ModeTheory -> Subst -> Context -> Either Text Context
applySubstCtx mt =
  U.applySubstCtx (modeOnlyTypeTheory mt)

unifyTyFlex :: ModeTheory -> S.Set TyVar -> Subst -> TypeExpr -> TypeExpr -> Either Text Subst
unifyTyFlex mt flex =
  U.unifyTyFlex (modeOnlyTypeTheory mt) [] flex S.empty

composeSubst :: ModeTheory -> Subst -> Subst -> Either Text Subst
composeSubst mt =
  U.composeSubst (modeOnlyTypeTheory mt)

freeTyVarsCtx :: Context -> S.Set TyVar
freeTyVarsCtx = S.unions . map freeTyVarsType


-- Public entrypoint

elabSurfaceExpr :: ModuleEnv -> Doctrine -> PolySurfaceDef -> Text -> Either Text (Doctrine, Diagram)
elabSurfaceExpr menv docS surf src = do
  let mode = psMode surf
  let mt = dModes docS
  let spec = psSpec surf
  node <- parseSurfaceExpr spec src
  ops <- requireStructuralOps menv docS mode
  env0 <- initEnv
  surfDiag <- evalFresh (elabNode menv docS mt mode ops env0 node)
  if M.null (sdUses surfDiag)
    then pure ()
    else Left "surface: unresolved variables"
  validateDiagram (sdDiag surfDiag)
  ensureAttrVarNameSortsDiagram (freeAttrVarsDiagram (sdDiag surfDiag))
  docBase <- resolveBaseDoctrine menv docS surf
  diagOut <-
    if dName docBase == dName docS
      then Right (sdDiag surfDiag)
      else eliminateToBase docS docBase mode (sdDiag surfDiag)
  validateDiagram diagOut
  ensureAttrVarNameSortsDiagram (freeAttrVarsDiagram diagOut)
  pure (docBase, diagOut)

resolveBaseDoctrine :: ModuleEnv -> Doctrine -> PolySurfaceDef -> Either Text Doctrine
resolveBaseDoctrine menv docS surf =
  case psBaseDoctrine surf of
    Nothing -> Right docS
    Just baseName ->
      if baseName == dName docS
        then Right docS
        else
          case M.lookup baseName (meDoctrines menv) of
            Nothing -> Left ("surface: unknown base doctrine: " <> baseName)
            Just docBase -> do
              let mode = psMode surf
              if M.member mode (mtModes (dModes docBase))
                then Right ()
                else Left "surface: base doctrine is missing surface mode"
              let gensS = genSetForMode docS mode
              let gensB = genSetForMode docBase mode
              if S.isSubsetOf gensB gensS
                then Right docBase
                else
                  let missing = S.toList (S.difference gensB gensS)
                   in Left ("surface: base generators are not included in surface doctrine: " <> renderGenList missing)

eliminateToBase :: Doctrine -> Doctrine -> ModeName -> Diagram -> Either Text Diagram
eliminateToBase docS docB mode diag0 = do
  let gensS = genSetForMode docS mode
  let gensB = genSetForMode docB mode
  let sigma = S.difference gensS gensB
  let rules0 = [ rr | rr <- rulesFromPolicy UseAllOriented (dCells2 docS), dMode (rrLHS rr) == mode ]
  let rulesElim =
        [ rr
        | rr <- rules0
        , surfaceMeasure sigma (rrLHS rr) > surfaceMeasure sigma (rrRHS rr)
        ]
  let fuel = surfaceMeasure sigma diag0
  status <- normalize (doctrineTypeTheory docS) fuel rulesElim diag0
  let diagNorm =
        case status of
          Finished d -> d
          OutOfFuel d -> d
  let remainingSurface = S.intersection sigma (gensInDiagram diagNorm)
  if S.null remainingSurface
    then Right ()
    else Left ("surface elimination did not reach base doctrine; remaining surface generators: " <> renderGenList (S.toList remainingSurface))
  let remainingOutsideBase = S.difference (gensInDiagram diagNorm) gensB
  if S.null remainingOutsideBase
    then Right diagNorm
    else Left ("surface elimination produced generators outside base doctrine: " <> renderGenList (S.toList remainingOutsideBase))

renderGenList :: [GenName] -> Text
renderGenList names =
  T.intercalate ", " [ g | GenName g <- sortByName names ]
  where
    sortByName = sortOnGen
    sortOnGen = sortByText . map unwrap
    unwrap gn@(GenName t) = (t, gn)
    sortByText xs = map snd (sort xs)

genSetForMode :: Doctrine -> ModeName -> S.Set GenName
genSetForMode doc mode = maybe S.empty M.keysSet (M.lookup mode (dGens doc))

gensInDiagram :: Diagram -> S.Set GenName
gensInDiagram diag =
  S.unions (map edgeGens (IM.elems (dEdges diag)))
  where
    edgeGens edge =
      case ePayload edge of
        PGen g _ bargs -> S.insert g (S.unions (map binderGens bargs))
        PBox _ inner -> gensInDiagram inner
        PFeedback inner -> gensInDiagram inner
        PSplice _ -> S.empty
        PTmMeta _ -> S.empty

    binderGens barg =
      case barg of
        BAConcrete inner -> gensInDiagram inner
        BAMeta _ -> S.empty

surfaceMeasure :: S.Set GenName -> Diagram -> Int
surfaceMeasure sigma diag =
  sum (map edgeMeasure (IM.elems (dEdges diag)))
  where
    edgeMeasure edge =
      case ePayload edge of
        PGen g _ bargs ->
          let own = if g `S.member` sigma then 1 else 0
           in own + sum (map binderMeasure bargs)
        PBox _ inner -> surfaceMeasure sigma inner
        PFeedback inner -> surfaceMeasure sigma inner
        PSplice _ -> 0
        PTmMeta _ -> 0

    binderMeasure barg =
      case barg of
        BAConcrete inner -> surfaceMeasure sigma inner
        BAMeta _ -> 0


-- Elaboration environment

data ElabEnv = ElabEnv
  { eeVars :: M.Map Text TypeExpr
  , eeTypeSubst :: Subst
  } deriving (Eq, Show)

initEnv :: Either Text ElabEnv
initEnv = Right (ElabEnv M.empty U.emptySubst)

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
              let checkParam (param, argTy) =
                    case param of
                      PS_Ty m ->
                        if typeMode argTy == m
                          then Right ()
                          else Left "surface: type constructor argument mode mismatch"
                      PS_Tm _ ->
                        Left "surface: term arguments are not supported in surface type annotations"
              mapM_ checkParam (zip params args')
              Right (Ty.TCon ref (map Ty.TAType args'))
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
mergeUses = M.unionWith (<>)

shiftUses :: Int -> Uses -> Uses
shiftUses off = M.map (map shiftPort)
  where
    shiftPort (PortId k) = PortId (k + off)

replacePortUses :: PortId -> PortId -> Uses -> Uses
replacePortUses keep drop = M.map (dedupe . map replace)
  where
    replace p = if p == drop then keep else p

mergeTags :: Tags -> Tags -> Tags
mergeTags = M.unionWith (<>)

shiftTags :: Int -> Tags -> Tags
shiftTags off = M.map (map shiftPort)
  where
    shiftPort (PortId k) = PortId (k + off)

replacePortTags :: PortId -> PortId -> Tags -> Tags
replacePortTags keep drop = M.map (dedupe . map replace)
  where
    replace p = if p == drop then keep else p

applySubstSurf :: ModeTheory -> Subst -> SurfDiag -> Either Text SurfDiag
applySubstSurf mt subst sd = do
  diag' <- applySubstDiagram (modeOnlyTypeTheory mt) subst (sdDiag sd)
  pure sd { sdDiag = diag' }


-- Structural discipline

data StructuralOp
  = SOGen TypeTheory GenDecl
  | SOFromImpl (TypeExpr -> Either Text Diagram)

data StructuralOps = StructuralOps
  { soDup :: Maybe StructuralOp
  , soDrop :: Maybe StructuralOp
  }

requireStructuralOps :: ModuleEnv -> Doctrine -> ModeName -> Either Text StructuralOps
requireStructuralOps menv doc mode = do
  implMorphs <- resolveImplMorphisms menv (dName doc)
  implDup <- resolveImplOp mode isDupShape implMorphs
  implDrop <- resolveImplOp mode isDropShape implMorphs
  pure
    StructuralOps
      { soDup = implDup
      , soDrop = implDrop
      }

data StructuralCandidate = StructuralCandidate
  { scMorphName :: Text
  , scIface :: Doctrine
  , scMorph :: PolyMorph.Morphism
  , scGen :: GenDecl
  }

resolveImplMorphisms :: ModuleEnv -> Text -> Either Text [(Text, Doctrine, PolyMorph.Morphism)]
resolveImplMorphisms menv targetName =
  fmap concat (mapM fromDefaultKey (M.toList (meImplDefaults menv)))
  where
    fromDefaultKey ((ifaceName, tgtName), morphNames)
      | tgtName /= targetName = Right []
      | otherwise = do
          ifaceDoc <-
            case M.lookup ifaceName (meDoctrines menv) of
              Nothing -> Left ("surface: unknown implements interface doctrine " <> ifaceName)
              Just d -> Right d
          fmap concat (mapM (resolveOne ifaceName ifaceDoc) morphNames)

    resolveOne ifaceName ifaceDoc morphName =
      case M.lookup morphName (meMorphisms menv) of
        Nothing -> Left ("surface: unknown implements morphism " <> morphName)
        Just mor ->
          if dName (PolyMorph.morSrc mor) == ifaceName && dName (PolyMorph.morTgt mor) == targetName
            then Right [(morphName, ifaceDoc, mor)]
            else Right []

resolveImplOp
  :: ModeName
  -> (GenDecl -> Bool)
  -> [(Text, Doctrine, PolyMorph.Morphism)]
  -> Either Text (Maybe StructuralOp)
resolveImplOp targetMode matchesShape implMorphs =
  case candidates of
    [] -> Right Nothing
    [cand] ->
      Right
        ( Just
            ( SOFromImpl
                (\ty -> instantiateImplUnaryGen (scIface cand) (scMorph cand) (scGen cand) ty)
            )
        )
    _ ->
      Left
        ( "surface: multiple structural capabilities match the required shape: "
            <> T.intercalate ", " (map renderCandidate candidates)
        )
  where
    candidates = concatMap collect implMorphs

    collect (morphName, iface, mor) =
      [ StructuralCandidate
          { scMorphName = morphName
          , scIface = iface
          , scMorph = mor
          , scGen = gd
          }
      | (srcMode, mappedMode) <- M.toList (PolyMorph.morModeMap mor)
      , mappedMode == targetMode
      , gd <- M.elems (M.findWithDefault M.empty srcMode (dGens iface))
      , matchesShape gd
      ]

    renderCandidate cand =
      dName (scIface cand) <> "." <> renderGenName (gdName (scGen cand)) <> " via " <> scMorphName cand

    renderGenName (GenName g) = g

instantiateImplUnaryGen :: Doctrine -> PolyMorph.Morphism -> GenDecl -> TypeExpr -> Either Text Diagram
instantiateImplUnaryGen iface mor g ty = do
  srcVar <-
    case gdTyVars g of
      [v] -> Right v
      _ -> Left "surface: structural schema generator must be unary polymorphic"
  dSchema <- instantiateUnaryGen (doctrineTypeTheory iface) g (Ty.TVar srcVar)
  dMapped <- PolyMorph.applyMorphismDiagram mor dSchema
  tgtMode <-
    case M.lookup (tvMode srcVar) (PolyMorph.morModeMap mor) of
      Nothing -> Left "surface: implements morphism is missing a mode mapping for structural schema"
      Just m -> Right m
  let tgtVar = srcVar { tvMode = tgtMode }
  applySubstDiagram
    (doctrineTypeTheory (PolyMorph.morTgt mor))
    (U.Subst { U.sTy = M.singleton tgtVar ty, U.sTm = M.empty })
    dMapped

isDupShape :: GenDecl -> Bool
isDupShape gen =
  case (gdTyVars gen, gdTmVars gen, gdAttrs gen, gdDom gen, gdCod gen) of
    ([v], [], [], [InPort (Ty.TVar v1)], [Ty.TVar v2, Ty.TVar v3]) ->
      v == v1 && v == v2 && v == v3
    _ -> False

isDropShape :: GenDecl -> Bool
isDropShape gen =
  case (gdTyVars gen, gdTmVars gen, gdAttrs gen, gdDom gen, gdCod gen) of
    ([v], [], [], [InPort (Ty.TVar v1)], []) -> v == v1
    _ -> False


-- Elaboration core

data RuntimeBinder
  = RBInput Text TypeExpr
  | RBValue Text Int
  deriving (Eq, Show)

elabNode :: ModuleEnv -> Doctrine -> ModeTheory -> ModeName -> StructuralOps -> ElabEnv -> SurfaceNode -> Fresh SurfDiag
elabNode menv doc mt mode ops env node = do
  typeSubst <- liftEither (buildTypeSubst doc mode env (snParams node))
  (mBinder, mBodyHole, bodyEnv) <- prepareBinder doc mode mt env (snParams node) (snBinder node)
  let children = snChildren node
  childDiags <-
    mapM
      (\(idx, child) ->
        let childEnv =
              case mBodyHole of
                Just bodyIdx | idx == bodyIdx -> bodyEnv
                _ -> env
         in elabNode menv doc mt mode ops childEnv child)
      (zip [1 ..] children)
  surf <- evalTemplate menv doc mt mode ops env (snParams node) typeSubst childDiags (snTemplate node)
  applyBinder mt doc mode ops mBinder surf

prepareBinder
  :: Doctrine
  -> ModeName
  -> ModeTheory
  -> ElabEnv
  -> M.Map Text SurfaceParam
  -> Maybe BinderDecl
  -> Fresh (Maybe RuntimeBinder, Maybe Int, ElabEnv)
prepareBinder _doc _mode _mt env _params Nothing =
  pure (Nothing, Nothing, env)
prepareBinder doc mode mt env params (Just decl) =
  case decl of
    BindIn varCap typeCap bodyHole -> do
      varName <- liftEither (requireIdentParam params varCap)
      tyRaw <- liftEither (requireTypeParam params typeCap)
      tyAnn <- liftEither (elabSurfaceTypeExpr doc mode tyRaw)
      if typeMode tyAnn /= mode
        then liftEither (Left "surface: binder type must be in surface mode")
        else pure ()
      ty <- liftEither (applySubstTy mt (eeTypeSubst env) tyAnn)
      let env' =
            env
              { eeVars = M.insert varName ty (eeVars env)
              }
      pure (Just (RBInput varName ty), Just bodyHole, env')
    BindLet varCap valueHole bodyHole -> do
      varName <- liftEither (requireIdentParam params varCap)
      fresh <- freshTyVar (TyVar { tvName = varName, tvMode = mode })
      let ty = Ty.TVar fresh
      let env' =
            env
              { eeVars = M.insert varName ty (eeVars env)
              }
      pure (Just (RBValue varName valueHole), Just bodyHole, env')

requireIdentParam :: M.Map Text SurfaceParam -> Text -> Either Text Text
requireIdentParam params cap =
  case M.lookup cap params of
    Just (SPIdent name) -> Right name
    _ -> Left ("surface: missing ident capture for " <> cap)

requireTypeParam :: M.Map Text SurfaceParam -> Text -> Either Text RawPolyTypeExpr
requireTypeParam params cap =
  case M.lookup cap params of
    Just (SPType ty) -> Right ty
    _ -> Left ("surface: missing <type> capture for " <> cap)

elabVarRef :: ModeTheory -> Subst -> Text -> TypeExpr -> Fresh SurfDiag
elabVarRef mt subst name ty = do
  ty' <- liftEither (applySubstTy mt subst ty)
  let base0 = varSurf name ty'
  liftEither (applySubstSurf mt subst base0)

elabZeroArgGen :: ModeTheory -> Doctrine -> ModeName -> ElabEnv -> Text -> Fresh SurfDiag
elabZeroArgGen mt doc mode env name = do
  gen <- liftEither (lookupGen doc mode (GenName name))
  liftEither (ensureDirectGenCallAttrs gen)
  if null (gdPlainDom gen)
    then do
      diag <- genDFromDecl mt mode env gen Nothing M.empty []
      pure (emptySurf diag)
    else liftEither (Left ("surface: unknown variable " <> name))

ensureDirectGenCallAttrs :: GenDecl -> Either Text ()
ensureDirectGenCallAttrs gen =
  if null (gdAttrs gen)
    then Right ()
    else Left "surface: generator requires attribute arguments; supply via a template action"


-- Template evaluation

evalTemplate
  :: ModuleEnv
  -> Doctrine
  -> ModeTheory
  -> ModeName
  -> StructuralOps
  -> ElabEnv
  -> M.Map Text SurfaceParam
  -> Subst
  -> [SurfDiag]
  -> TemplateExpr
  -> Fresh SurfDiag
evalTemplate menv doc mt mode ops env paramMap subst childList templ =
  case templ of
    THole n ->
      case drop (n - 1) childList of
        (sd : _) -> pure (tagHole n sd { sdTags = M.empty })
        [] -> liftEither (Left "surface: template hole out of range")
    TVar cap -> do
      varName <-
        case M.lookup cap paramMap of
          Just (SPIdent v) -> pure v
          _ -> liftEither (Left ("surface: variable placeholder requires ident capture: " <> cap))
      case M.lookup varName (eeVars env) of
        Nothing -> elabZeroArgGen mt doc mode env varName
        Just ty -> elabVarRef mt subst varName ty
    TTermRef name ->
      case M.lookup name (meTerms menv) of
        Nothing -> liftEither (Left ("surface: unknown term reference @" <> name))
        Just td ->
          if tdDoctrine td /= dName doc
            then liftEither (Left ("surface: term @" <> name <> " doctrine mismatch"))
            else
              if tdMode td /= mode
                then liftEither (Left ("surface: term @" <> name <> " mode mismatch"))
                else pure (emptySurf (tdDiagram td))
    TId ctx -> do
      ctx'0 <- liftEither (mapM (elabSurfaceTypeExpr doc mode) ctx)
      ctx' <- liftEither (mapM (applySubstTy mt subst) ctx'0)
      pure (emptySurf (idD mode ctx'))
    TGen ref mArgs mAttrArgs mBinderArgs -> do
      genName <-
        case ref of
          GenLit name -> pure name
          GenHole cap ->
            case M.lookup cap paramMap of
              Just (SPIdent name) -> pure name
              _ -> liftEither (Left ("surface: generator hole requires ident capture: " <> cap))
      gen <- liftEither (lookupGen doc mode (GenName genName))
      args0 <-
        case mArgs of
          Nothing -> pure Nothing
          Just args -> do
            tys <- liftEither (mapM (elabSurfaceTypeExpr doc mode) args)
            pure (Just tys)
      args' <-
        liftEither
          ( case args0 of
              Nothing -> Right Nothing
              Just args -> Just <$> mapM (applySubstTy mt subst) args
          )
      attrs <- liftEither (elabTemplateGenAttrs doc gen paramMap mAttrArgs)
      bargs <- evalTemplateBinderArgs menv doc mt mode ops env paramMap subst childList mBinderArgs
      diag <- genDFromDecl mt mode env gen args' attrs bargs
      pure (emptySurf diag)
    TBox name inner -> do
      innerDiag <- evalTemplate menv doc mt mode ops env paramMap subst childList inner
      liftEither (boxSurf mode name innerDiag)
    TLoop inner -> do
      innerDiag <- evalTemplate menv doc mt mode ops env paramMap subst childList inner
      liftEither (loopSurf innerDiag)
    TComp a b -> do
      d1 <- evalTemplate menv doc mt mode ops env paramMap subst childList a
      d2 <- evalTemplate menv doc mt mode ops env paramMap subst childList b
      liftEither (compSurf mt d1 d2)
    TTensor a b -> do
      d1 <- evalTemplate menv doc mt mode ops env paramMap subst childList a
      d2 <- evalTemplate menv doc mt mode ops env paramMap subst childList b
      liftEither (tensorSurf d1 d2)

evalTemplateBinderArgs
  :: ModuleEnv
  -> Doctrine
  -> ModeTheory
  -> ModeName
  -> StructuralOps
  -> ElabEnv
  -> M.Map Text SurfaceParam
  -> Subst
  -> [SurfDiag]
  -> Maybe [TemplateBinderArg]
  -> Fresh [BinderArg]
evalTemplateBinderArgs _menv _doc _mt _mode _ops _env _paramMap _subst _children Nothing =
  pure []
evalTemplateBinderArgs menv doc mt mode ops env paramMap subst children (Just args) =
  mapM evalOne args
  where
    evalOne arg =
      case arg of
        TBAMeta name -> pure (BAMeta (BinderMetaVar name))
        TBAExpr expr -> do
          sd <- evalTemplate menv doc mt mode ops env paramMap subst children expr
          if M.null (sdUses sd)
            then do
              liftEither (validateDiagram (sdDiag sd))
              pure (BAConcrete (sdDiag sd))
            else liftEither (Left "surface: binder argument uses unresolved surface variables")

buildTypeSubst :: Doctrine -> ModeName -> ElabEnv -> M.Map Text SurfaceParam -> Either Text Subst
buildTypeSubst doc mode env paramMap = do
  pairs <- mapM toPair (M.toList paramMap)
  let localTy = M.fromList (concat pairs)
      envSub = eeTypeSubst env
  pure envSub { U.sTy = M.union localTy (U.sTy envSub) }
  where
    toPair (name, param) =
      case param of
        SPType rawTy -> do
          ty <- elabSurfaceTypeExpr doc mode rawTy
          let var = TyVar { tvName = name, tvMode = mode }
          pure [(var, ty)]
        _ -> pure []

elabTemplateGenAttrs
  :: Doctrine
  -> GenDecl
  -> M.Map Text SurfaceParam
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
    (_ : _, _ : _) -> Left "surface: template attribute arguments must be either all named or all positional"
    (_ : _, []) -> normalizeNamed namedArgs
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

elabTemplateAttrTerm :: Doctrine -> AttrSort -> M.Map Text SurfaceParam -> AttrTemplate -> Either Text AttrTerm
elabTemplateAttrTerm doc expectedSort paramMap termTemplate =
  case termTemplate of
    ATLIT lit -> do
      ensureLiteralAllowed doc expectedSort lit
      Right (ATLit lit)
    ATHole name ->
      case M.lookup name paramMap of
        Just (SPLit lit) -> do
          ensureLiteralAllowed doc expectedSort lit
          Right (ATLit lit)
        Just (SPIdent identName) -> do
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

applyBinder :: ModeTheory -> Doctrine -> ModeName -> StructuralOps -> Maybe RuntimeBinder -> SurfDiag -> Fresh SurfDiag
applyBinder _mt _doc _mode _ops Nothing sd = pure sd
applyBinder mt doc mode ops (Just binder) sd =
  case binder of
    RBInput varName varTy -> do
      let (source, diag1) = freshPort varTy (sdDiag sd)
      diag1a <- liftEither (setPortLabel source varName diag1)
      let sd1 = sd { sdDiag = diag1a }
      connectVar doc mode ops varName source varTy sd1 True
    RBValue varName valueHole -> do
      let ports = M.findWithDefault [] (TagHole valueHole) (sdTags sd)
      case ports of
        [source] -> do
          ty <-
            case diagramPortType (sdDiag sd) source of
              Nothing -> liftEither (Left "surface: missing bound value type")
              Just t -> pure t
          sd1 <- unifyVarType mt varName ty sd
          diagLabeled <- liftEither (setPortLabel source varName (sdDiag sd1))
          let sd1a = sd1 { sdDiag = diagLabeled }
          sd2 <- connectVar doc mode ops varName source ty sd1a False
          let tags' = M.delete (TagHole valueHole) (sdTags sd2)
          pure sd2 { sdTags = tags' }
        _ ->
          let count = length ports
           in liftEither (Left ("surface: bound value must have exactly one output (" <> T.pack (show count) <> ")"))

unifyVarType :: ModeTheory -> Text -> TypeExpr -> SurfDiag -> Fresh SurfDiag
unifyVarType mt varName ty sd =
  case M.lookup varName (sdUses sd) of
    Nothing -> pure sd
    Just [] -> pure sd
    Just (p : _) ->
      case diagramPortType (sdDiag sd) p of
        Nothing -> pure sd
        Just tyUse -> do
          let flex = S.union (freeTyVarsType tyUse) (freeTyVarsType ty)
          subst <- liftEither (unifyTyFlex mt flex U.emptySubst tyUse ty)
          liftEither (applySubstSurf mt subst sd)

connectVar :: Doctrine -> ModeName -> StructuralOps -> Text -> PortId -> TypeExpr -> SurfDiag -> Bool -> Fresh SurfDiag
connectVar _doc _mode ops varName source ty sd sourceIsInput = do
  let uses = M.findWithDefault [] varName (sdUses sd)
  let useInOutput = any (`elem` dOut (sdDiag sd)) uses
  sd1 <- connectUses ops varName source ty uses sd
  let diag1 = sdDiag sd1
  let dIn' = if sourceIsInput then ensureIn source (dIn diag1) else removePort source (dIn diag1)
  let dOut' =
        if sourceIsInput
          then dOut diag1
          else
            if useInOutput
              then dOut diag1
              else removePort source (dOut diag1)
  let diag2 = diag1 { dIn = dIn', dOut = dOut' }
  pure sd1 { sdDiag = diag2, sdUses = M.delete varName (sdUses sd1) }
  where
    ensureIn p xs = if p `elem` xs then xs else p : xs
    removePort p = filter (/= p)

connectUses :: StructuralOps -> Text -> PortId -> TypeExpr -> [PortId] -> SurfDiag -> Fresh SurfDiag
connectUses ops varName source ty uses sd =
  case uses of
    [] ->
      case soDrop ops of
        Just dropOp -> addDrop dropOp
        Nothing ->
          liftEither (Left ("surface: variable " <> varName <> " dropped but no drop capability is implemented"))
    [p] -> do
      (diag1, uses1, tags1) <- mergePortsAll source p sd
      pure sd { sdDiag = diag1, sdUses = uses1, sdTags = tags1 }
    _ ->
      case soDup ops of
        Just dupOp -> addDup dupOp
        Nothing ->
          liftEither (Left ("surface: variable " <> varName <> " duplicated but no dup capability is implemented"))
  where
    addDrop dropOp = do
      let diag0 = sdDiag sd
      dropDiag <- liftEither (instantiateStructuralOp dropOp ty)
      (outs, diag1) <- liftEither (attachUnaryDiagram source diag0 dropDiag)
      if null outs
        then pure sd { sdDiag = diag1 }
        else liftEither (Left "surface: drop capability must have codomain []")

    addDup dupOp = do
      (outs, diag1) <- dupOutputs dupOp source ty (sdDiag sd) (length uses)
      let sd1 = sd { sdDiag = diag1 }
      foldM mergeOne sd1 (zip outs uses)

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


-- Duplication tree (left-associated)

dupOutputs :: StructuralOp -> PortId -> TypeExpr -> Diagram -> Int -> Fresh ([PortId], Diagram)
dupOutputs dupOp source ty diag n
  | n <= 0 = pure ([], diag)
  | n == 1 = pure ([source], diag)
  | otherwise = do
      dupDiag <- liftEither (instantiateStructuralOp dupOp ty)
      (outs, diag1) <- liftEither (attachUnaryDiagram source diag dupDiag)
      (p1, p2) <-
        case outs of
          [a, b] -> pure (a, b)
          _ -> liftEither (Left "surface: dup capability must have codomain [a, a]")
      (leftOuts, diag2) <- dupOutputs dupOp p1 ty diag1 (n - 1)
      let diag3 = diag2 { dIn = filter (/= p1) (dIn diag2) }
      pure (leftOuts ++ [p2], diag3)

instantiateStructuralOp :: StructuralOp -> TypeExpr -> Either Text Diagram
instantiateStructuralOp op ty =
  case op of
    SOGen tt gen ->
      instantiateUnaryGen tt gen ty
    SOFromImpl mkDiag ->
      mkDiag ty

attachUnaryDiagram :: PortId -> Diagram -> Diagram -> Either Text ([PortId], Diagram)
attachUnaryDiagram source host op = do
  if dMode op /= dMode host
    then Left "surface: structural capability has wrong mode"
    else Right ()
  if dTmCtx op /= dTmCtx host
    then Left "surface: structural capability has incompatible term context"
    else Right ()
  case dIn op of
    [_] -> Right ()
    _ -> Left "surface: structural capability must be unary"
  let opShift = shiftDiagram (dNextPort host) (dNextEdge host) op
  merged <- unionDiagram host opShift
  inShift <-
    case dIn opShift of
      [p] -> Right p
      _ -> Left "surface: structural capability must remain unary after shift"
  merged' <- mergePorts merged source inShift
  pure (dOut opShift, merged')

instantiateUnaryGen :: TypeTheory -> GenDecl -> TypeExpr -> Either Text Diagram
instantiateUnaryGen tt gen ty = do
  ensureStructuralGenAttrs gen
  if not (null (gdTmVars gen))
    then Left "surface: structural generator must not have term parameters"
    else Right ()
  if any isBinder (gdDom gen)
    then Left "surface: structural generator must not have binder slots"
    else Right ()
  substTy <- case gdTyVars gen of
    [v] -> Right (M.singleton v ty)
    [] -> Right M.empty
    _ -> Left "surface: structural generator must be unary polymorphic in exactly one type variable"
  let subst = U.Subst { U.sTy = substTy, U.sTm = M.empty }
  dom <- U.applySubstCtx tt subst (gdPlainDom gen)
  cod <- U.applySubstCtx tt subst (gdCod gen)
  genD (gdMode gen) dom cod (gdName gen)
  where
    isBinder sh =
      case sh of
        InPort _ -> False
        InBinder _ -> True

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

varSurf :: Text -> TypeExpr -> SurfDiag
varSurf name ty =
  let mode = typeMode ty
      diag = idD mode [ty]
   in SurfDiag diag (M.singleton name (dIn diag)) M.empty


-- Diagram construction helpers

lookupGen :: Doctrine -> ModeName -> GenName -> Either Text GenDecl
lookupGen doc mode name =
  case M.lookup mode (dGens doc) >>= M.lookup name of
    Nothing -> Left ("surface: unknown generator: " <> renderGen name <> " @" <> renderMode mode)
    Just gd -> Right gd
  where
    renderMode (ModeName m) = m
    renderGen (GenName g) = g

genDFromDecl :: ModeTheory -> ModeName -> ElabEnv -> GenDecl -> Maybe [TypeExpr] -> AttrMap -> [BinderArg] -> Fresh Diagram
genDFromDecl mt mode env gen mArgs attrs bargs = do
  let tyVars = gdTyVars gen
  let subst0 = eeTypeSubst env
  renameSubst <- freshSubst tyVars
  dom0 <- liftEither (applySubstCtx mt renameSubst (gdPlainDom gen))
  cod0 <- liftEither (applySubstCtx mt renameSubst (gdCod gen))
  slots0 <- liftEither (mapM (applySubstBinderSigTy mt renameSubst) [ bs | InBinder bs <- gdDom gen ])
  dom1 <- liftEither (applySubstCtx mt subst0 dom0)
  cod1 <- liftEither (applySubstCtx mt subst0 cod0)
  slots1 <- liftEither (mapM (applySubstBinderSigTy mt subst0) slots0)
  (dom2, cod2, slots2) <-
    case mArgs of
      Nothing -> pure (dom1, cod1, slots1)
      Just args -> do
        args' <- liftEither (mapM (applySubstTy mt subst0) args)
        if length args' /= length tyVars
          then liftEither (Left "surface: generator type argument mismatch")
          else do
            freshVars <- liftEither (extractFreshVars tyVars renameSubst)
            let subst = U.Subst (M.fromList (zip freshVars args')) M.empty
            dom2' <- liftEither (applySubstCtx mt subst dom1)
            cod2' <- liftEither (applySubstCtx mt subst cod1)
            slots2' <- liftEither (mapM (applySubstBinderSigTy mt subst) slots1)
            pure (dom2', cod2', slots2')
  (domFinal, codFinal, bargsFinal) <- liftEither (checkBinderArgs mt dom2 cod2 slots2 bargs)
  liftEither (buildGenDiagram mode domFinal codFinal (gdName gen) attrs bargsFinal)

applySubstBinderSigTy :: ModeTheory -> Subst -> BinderSig -> Either Text BinderSig
applySubstBinderSigTy mt subst bs = do
  tmCtx' <- mapM (applySubstTy mt subst) (bsTmCtx bs)
  dom' <- applySubstCtx mt subst (bsDom bs)
  cod' <- applySubstCtx mt subst (bsCod bs)
  pure bs { bsTmCtx = tmCtx', bsDom = dom', bsCod = cod' }

checkBinderArgs
  :: ModeTheory
  -> Context
  -> Context
  -> [BinderSig]
  -> [BinderArg]
  -> Either Text (Context, Context, [BinderArg])
checkBinderArgs mt dom cod slots args =
  case (slots, args) of
    ([], []) -> Right (dom, cod, [])
    ([], _ : _) -> Left "surface: generator does not accept binder arguments"
    (_ : _, []) -> Left "surface: missing generator binder arguments"
    _ ->
      if length slots /= length args
        then Left "surface: generator binder argument mismatch"
        else do
          (substFinal, checked0) <- foldM step (U.emptySubst, []) (zip slots args)
          domFinal <- applySubstCtx mt substFinal dom
          codFinal <- applySubstCtx mt substFinal cod
          checked <- mapM (applySubstBinderArg mt substFinal) checked0
          Right (domFinal, codFinal, checked)
  where
    step (substAcc, out) (slot0, barg0) =
      case barg0 of
        BAMeta _ -> Right (substAcc, out <> [barg0])
        BAConcrete inner0 -> do
          slot <- applySubstBinderSigTy mt substAcc slot0
          inner <- applySubstDiagram (modeOnlyTypeTheory mt) substAcc inner0
          domArg <- diagramDom inner
          let flexDom = S.union (freeTyVarsCtx (bsDom slot)) (freeTyVarsCtx domArg)
          sDom <- U.unifyCtx (modeOnlyTypeTheory mt) [] flexDom S.empty (bsDom slot) domArg
          subst1 <- composeSubst mt sDom substAcc
          slot1 <- applySubstBinderSigTy mt sDom slot
          inner1 <- applySubstDiagram (modeOnlyTypeTheory mt) sDom inner
          codArg <- diagramCod inner1
          let flexCod = S.union (freeTyVarsCtx (bsCod slot1)) (freeTyVarsCtx codArg)
          sCod <- U.unifyCtx (modeOnlyTypeTheory mt) [] flexCod S.empty (bsCod slot1) codArg
          subst2 <- composeSubst mt sCod subst1
          inner2 <- applySubstDiagram (modeOnlyTypeTheory mt) sCod inner1
          Right (subst2, out <> [BAConcrete inner2])

applySubstBinderArg :: ModeTheory -> Subst -> BinderArg -> Either Text BinderArg
applySubstBinderArg mt subst barg =
  case barg of
    BAMeta _ -> Right barg
    BAConcrete inner ->
      BAConcrete <$> applySubstDiagram (modeOnlyTypeTheory mt) subst inner

buildGenDiagram :: ModeName -> Context -> Context -> GenName -> AttrMap -> [BinderArg] -> Either Text Diagram
buildGenDiagram mode dom cod gen attrs bargs = do
  let (inPorts, diag1) = allocPorts dom (emptyDiagram mode [])
  let (outPorts, diag2) = allocPorts cod diag1
  diag3 <- addEdgePayload (PGen gen attrs bargs) inPorts outPorts diag2
  let diagFinal = diag3 { dIn = inPorts, dOut = outPorts }
  validateDiagram diagFinal
  pure diagFinal

allocPorts :: Context -> Diagram -> ([PortId], Diagram)
allocPorts [] diag = ([], diag)
allocPorts (ty : rest) diag =
  let (pid, diag1) = freshPort ty diag
      (pids, diag2) = allocPorts rest diag1
   in (pid : pids, diag2)


-- Composition with tags and uses

compSurf :: ModeTheory -> SurfDiag -> SurfDiag -> Either Text SurfDiag
compSurf mt a b = do
  codA <- diagramCod (sdDiag a)
  domB <- diagramDom (sdDiag b)
  let flex = S.union (freeTyVarsDiagram (sdDiag a)) (freeTyVarsDiagram (sdDiag b))
  subst <- U.unifyCtx (modeOnlyTypeTheory mt) [] flex S.empty codA domB
  a' <- applySubstSurf mt subst a
  b' <- applySubstSurf mt subst b
  let bShift = shiftDiagram (dNextPort (sdDiag a')) (dNextEdge (sdDiag a')) (sdDiag b')
  let usesShift = shiftUses (dNextPort (sdDiag a')) (sdUses b')
  let tagsShift = shiftTags (dNextPort (sdDiag a')) (sdTags b')
  merged <- unionDiagram (sdDiag a') bShift
  let merged0 = merged { dIn = dIn (sdDiag a'), dOut = dOut bShift }
  (diagFinal, usesFinal, tagsFinal) <-
    foldM
      mergeStep
      (merged0, mergeUses (sdUses a') usesShift, mergeTags (sdTags a') tagsShift)
      (zip (dOut (sdDiag a')) (dIn bShift))
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
  pure
    SurfDiag
      { sdDiag = diagFinal
      , sdUses = mergeUses (sdUses a) usesShift
      , sdTags = mergeTags (sdTags a) tagsShift
      }

boxSurf :: ModeName -> Text -> SurfDiag -> Either Text SurfDiag
boxSurf mode name inner = do
  dom <- diagramDom (sdDiag inner)
  cod <- diagramCod (sdDiag inner)
  let (ins, diag0) = allocPorts dom (emptyDiagram mode [])
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
    ([pIn], pState : pOuts) -> do
      stateInTy <- requirePortTy (sdDiag sd) pIn
      stateOutTy <- requirePortTy (sdDiag sd) pState
      if stateInTy == stateOutTy
        then Right ()
        else Left "loop: body first output type must match input type"
      outTys <- mapM (requirePortTy (sdDiag sd)) pOuts
      let (outs, diag0) = allocPorts outTys (emptyDiagram (dMode (sdDiag sd)) (dTmCtx (sdDiag sd)))
      diag1 <- addEdgePayload (PFeedback (sdDiag sd)) [] outs diag0
      let diag2 = diag1 { dIn = [], dOut = outs }
      validateDiagram diag2
      let mapping = M.fromList (zip pOuts outs)
      let remap p = M.findWithDefault p p mapping
      let uses' = M.map (map remap) (sdUses sd)
      let tags' = M.map (map remap) (sdTags sd)
      pure sd { sdDiag = diag2, sdUses = uses', sdTags = tags' }
    _ -> Left "loop: expected exactly one input and at least one output"
  where
    requirePortTy d p =
      case diagramPortType d p of
        Nothing -> Left "loop: internal missing port type"
        Just ty -> Right ty

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

newtype Fresh a = Fresh (Int -> Either Text (a, Int))

instance Functor Fresh where
  fmap f (Fresh g) =
    Fresh
      (\n -> do
        (a, n') <- g n
        pure (f a, n'))

instance Applicative Fresh where
  pure a = Fresh (\n -> Right (a, n))
  Fresh f <*> Fresh g =
    Fresh
      (\n -> do
        (h, n1) <- f n
        (a, n2) <- g n1
        pure (h a, n2))

instance Monad Fresh where
  Fresh g >>= k =
    Fresh
      (\n -> do
        (a, n1) <- g n
        let Fresh h = k a
        h n1)

evalFresh :: Fresh a -> Either Text a
evalFresh (Fresh f) = fmap fst (f 0)

freshSubst :: [TyVar] -> Fresh Subst
freshSubst vars = do
  pairs <- mapM freshVar vars
  pure (U.Subst (M.fromList pairs) M.empty)

extractFreshVars :: [TyVar] -> Subst -> Either Text [TyVar]
extractFreshVars vars subst =
  mapM lookupVar vars
  where
    lookupVar v =
      case M.lookup v (U.sTy subst) of
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
