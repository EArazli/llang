{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.DSL.Elab
  ( elabPolyDoctrine
  , elabPolyMorphism
  , elabPolyRun
  , elabDiagExpr
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Control.Monad (foldM)
import Strat.DSL.AST (RawRun(..), RawRunShow(..), RawPolyMorphism(..), RawPolyMorphismItem(..), RawPolyTypeMap(..), RawPolyGenMap(..))
import Strat.Poly.DSL.AST
import Strat.Poly.Doctrine
import Strat.Poly.Diagram
import Strat.Poly.Graph (emptyDiagram, freshPort, addEdgePayload, EdgePayload(..), validateDiagram, mergePorts)
import Strat.Poly.ModeTheory
import Strat.Poly.Names
import Strat.Poly.TypeExpr
import Strat.Poly.UnifyTy
import Strat.Poly.Morphism
import Strat.Frontend.Env (ModuleEnv(..))
import Strat.Poly.Cell2 (Cell2(..))
import Strat.Common.Rules (RewritePolicy(..))
import Strat.RunSpec (RunShow(..), RunSpec(..))


elabPolyRun :: Text -> RawRun -> Either Text RunSpec
elabPolyRun name raw = do
  doctrine <- maybe (Left "run: missing doctrine") Right (rrDoctrine raw)
  let fuel = maybe 50 id (rrFuel raw)
  let flags = if null (rrShowFlags raw) then [ShowNormalized] else map toShow (rrShowFlags raw)
  let policyName = maybe "UseStructuralAsBidirectional" id (rrPolicy raw)
  policy <- parsePolicy policyName
  ensureShowFlags flags
  pure RunSpec
    { prName = name
    , prDoctrine = doctrine
    , prMode = rrMode raw
    , prSurface = rrSurface raw
    , prModel = rrModel raw
    , prMorphisms = rrMorphisms raw
    , prUses = rrUses raw
    , prPolicy = policy
    , prFuel = fuel
    , prShowFlags = flags
    , prExprText = rrExprText raw
    }
  where
    toShow s =
      case s of
        RawShowNormalized -> ShowNormalized
        RawShowInput -> ShowInput
        RawShowValue -> ShowValue
        RawShowCat -> ShowCat
        RawShowCoherence -> ShowCoherence
    ensureShowFlags flags =
      if ShowCat `elem` flags
        then Left "run: show cat is not supported"
        else if ShowValue `elem` flags && rrModel raw == Nothing
          then Left "run: show value requires model"
          else Right ()

elabPolyMorphism :: ModuleEnv -> RawPolyMorphism -> Either Text Morphism
elabPolyMorphism env raw = do
  src <- lookupPolyDoctrine env (rpmSrc raw)
  tgt <- lookupPolyDoctrine env (rpmTgt raw)
  let policyName = maybe "UseStructuralAsBidirectional" id (rpmPolicy raw)
  policy <- parsePolicy policyName
  let fuel = maybe 50 id (rpmFuel raw)
  typeMap <- foldM (addTypeMap src tgt) M.empty [ t | RPMType t <- rpmItems raw ]
  genMap <- foldM (addGenMap src tgt) M.empty [ g | RPMGen g <- rpmItems raw ]
  ensureAllGenMapped src genMap
  let mor = Morphism
        { morName = rpmName raw
        , morSrc = src
        , morTgt = tgt
        , morTypeMap = typeMap
        , morGenMap = genMap
        , morPolicy = policy
        , morFuel = fuel
        }
  case checkMorphism mor of
    Left err -> Left ("morphism " <> rpmName raw <> ": " <> err)
    Right () -> Right mor
  where
    lookupPolyDoctrine env' name =
      case M.lookup name (meDoctrines env') of
        Nothing -> Left ("Unknown doctrine: " <> name)
        Just doc -> Right doc
    addTypeMap src tgt mp decl = do
      let modeSrc = ModeName (rpmtSrcMode decl)
      let modeTgt = ModeName (rpmtTgtMode decl)
      if modeSrc /= modeTgt
        then Left "morphism: mode mapping not supported"
        else Right ()
      ensureMode src modeSrc
      ensureMode tgt modeSrc
      let name = TypeName (rpmtSrcType decl)
      let ref = TypeRef modeSrc name
      sig <- lookupTypeSig src ref
      params <- buildTypeMapParams (tsParams sig) (rpmtParams decl)
      tgtExpr <- elabTypeExpr tgt params (rpmtTgtType decl)
      let key = TypeRef modeSrc name
      if M.member key mp
        then Left "morphism: duplicate type mapping"
        else Right (M.insert key (TypeTemplate params tgtExpr) mp)
    addGenMap src tgt mp decl = do
      let mode = ModeName (rpmgMode decl)
      ensureMode src mode
      ensureMode tgt mode
      gen <- lookupGen src mode (GenName (rpmgSrcGen decl))
      let tyVars = gdTyVars gen
      diag <- elabDiagExpr tgt mode tyVars (rpmgRhs decl)
      let free = freeTyVarsDiagram diag
      let allowed = S.fromList tyVars
      if S.isSubsetOf free allowed
        then Right ()
        else Left "morphism: generator mapping uses undeclared type variables"
      let key = (mode, gdName gen)
      if M.member key mp
        then Left "morphism: duplicate generator mapping"
        else Right (M.insert key diag mp)
    -- no template restriction; any target type expression using only params is allowed
    ensureAllGenMapped src mp = do
      let gens = [ (mode, gdName g) | (mode, table) <- M.toList (dGens src), g <- M.elems table ]
      case [ (m, g) | (m, g) <- gens, M.notMember (m, g) mp ] of
        [] -> Right ()
        _ -> Left "morphism: missing generator mapping"

parsePolicy :: Text -> Either Text RewritePolicy
parsePolicy name =
  case name of
    "UseOnlyComputationalLR" -> Right UseOnlyComputationalLR
    "UseStructuralAsBidirectional" -> Right UseStructuralAsBidirectional
    "UseAllOriented" -> Right UseAllOriented
    _ -> Left ("Unknown policy: " <> name)

elabPolyDoctrine :: ModuleEnv -> RawPolyDoctrine -> Either Text Doctrine
elabPolyDoctrine env raw = do
  base <- case rpdExtends raw of
    Nothing -> Right Nothing
    Just name ->
      case M.lookup name (meDoctrines env) of
        Nothing -> Left ("Unknown doctrine: " <> name)
        Just doc -> Right (Just doc)
  let start = seedDoctrine (rpdName raw) base
  doc <- foldM (elabPolyItem env) start (rpdItems raw)
  validateDoctrine doc
  pure doc

seedDoctrine :: Text -> Maybe Doctrine -> Doctrine
seedDoctrine name base =
  case base of
    Nothing -> Doctrine
      { dName = name
      , dModes = emptyModeTheory
      , dTypes = M.empty
      , dGens = M.empty
      , dCells2 = []
      }
    Just doc -> doc { dName = name }

elabPolyItem :: ModuleEnv -> Doctrine -> RawPolyItem -> Either Text Doctrine
elabPolyItem _ doc item =
  case item of
    RPMode name -> do
      let mode = ModeName name
      mt' <- addMode mode (dModes doc)
      pure doc { dModes = mt' }
    RPType decl -> do
      let mode = ModeName (rptMode decl)
      ensureMode doc mode
      let tname = TypeName (rptName decl)
      ensureDistinctRawTyVarNames "duplicate type parameter name" (rptVars decl)
      sigModes <- mapM (resolveTyVarMode doc mode) (rptVars decl)
      let sig = TypeSig { tsParams = sigModes }
      let table = M.findWithDefault M.empty mode (dTypes doc)
      if M.member tname table
        then Left "duplicate type name"
        else do
          let table' = M.insert tname sig table
          let types' = M.insert mode table' (dTypes doc)
          pure doc { dTypes = types' }
    RPGen decl -> do
      let mode = ModeName (rpgMode decl)
      ensureMode doc mode
      let gname = GenName (rpgName decl)
      vars <- mapM (resolveTyVarDecl doc mode) (rpgVars decl)
      ensureDistinctTyVarNames "duplicate generator type parameter name" vars
      dom <- elabContext doc mode vars (rpgDom decl)
      cod <- elabContext doc mode vars (rpgCod decl)
      let gen = GenDecl
            { gdName = gname
            , gdMode = mode
            , gdTyVars = vars
            , gdDom = dom
            , gdCod = cod
            }
      let table = M.findWithDefault M.empty mode (dGens doc)
      if M.member gname table
        then Left "duplicate generator name"
        else do
          let table' = M.insert gname gen table
          let gens' = M.insert mode table' (dGens doc)
          pure doc { dGens = gens' }
    RPRule decl -> do
      let mode = ModeName (rprMode decl)
      ensureMode doc mode
      ruleVars <- mapM (resolveTyVarDecl doc mode) (rprVars decl)
      ensureDistinctTyVarNames "duplicate rule type parameter name" ruleVars
      dom <- elabContext doc mode ruleVars (rprDom decl)
      cod <- elabContext doc mode ruleVars (rprCod decl)
      lhs <- withRule (elabDiagExpr doc mode ruleVars (rprLHS decl))
      rhs <- withRule (elabDiagExpr doc mode ruleVars (rprRHS decl))
      let rigid = S.fromList ruleVars
      lhs' <- unifyBoundary rigid dom cod lhs
      rhs' <- unifyBoundary rigid dom cod rhs
      let free = S.union (freeTyVarsDiagram lhs') (freeTyVarsDiagram rhs')
      let allowed = S.fromList ruleVars
      if S.isSubsetOf free allowed
        then pure ()
        else Left ("rule " <> rprName decl <> ": unresolved type variables")
      let cell = Cell2
            { c2Name = rprName decl
            , c2Class = rprClass decl
            , c2Orient = rprOrient decl
            , c2TyVars = ruleVars
            , c2LHS = lhs'
            , c2RHS = rhs'
            }
      pure doc { dCells2 = dCells2 doc <> [cell] }
      where
        withRule action =
          case action of
            Left err -> Left ("rule " <> rprName decl <> ": " <> err)
            Right x -> Right x

ensureMode :: Doctrine -> ModeName -> Either Text ()
ensureMode doc mode =
  if mode `S.member` mtModes (dModes doc)
    then Right ()
    else Left "unknown mode"

resolveTyVarMode :: Doctrine -> ModeName -> RawTyVarDecl -> Either Text ModeName
resolveTyVarMode doc defaultMode decl = do
  let mode = maybe defaultMode ModeName (rtvMode decl)
  ensureMode doc mode
  pure mode

resolveTyVarDecl :: Doctrine -> ModeName -> RawTyVarDecl -> Either Text TyVar
resolveTyVarDecl doc defaultMode decl = do
  mode <- resolveTyVarMode doc defaultMode decl
  pure TyVar { tvName = rtvName decl, tvMode = mode }

ensureDistinctRawTyVarNames :: Text -> [RawTyVarDecl] -> Either Text ()
ensureDistinctRawTyVarNames label vars =
  let names = map rtvName vars
      set = S.fromList names
  in if S.size set == length names then Right () else Left label

ensureDistinctTyVarNames :: Text -> [TyVar] -> Either Text ()
ensureDistinctTyVarNames label vars =
  let names = map tvName vars
      set = S.fromList names
  in if S.size set == length names then Right () else Left label

lookupTyVarByName :: [TyVar] -> Text -> Either Text TyVar
lookupTyVarByName vars name =
  case [v | v <- vars, tvName v == name] of
    [v] -> Right v
    [] -> Left ("unknown type variable: " <> name)
    _ -> Left ("duplicate type variable name: " <> name)

resolveTypeRef :: Doctrine -> RawTypeRef -> Either Text TypeRef
resolveTypeRef doc raw =
  case rtrMode raw of
    Just modeName -> do
      let mode = ModeName modeName
      ensureMode doc mode
      let tname = TypeName (rtrName raw)
      case M.lookup mode (dTypes doc) >>= M.lookup tname of
        Nothing -> Left ("unknown type constructor: " <> rtrName raw)
        Just _ -> Right (TypeRef mode tname)
    Nothing -> do
      let tname = TypeName (rtrName raw)
      let matches =
            [ mode
            | (mode, table) <- M.toList (dTypes doc)
            , M.member tname table
            ]
      case matches of
        [] -> Left ("unknown type constructor: " <> rtrName raw)
        [mode] -> Right (TypeRef mode tname)
        _ -> Left ("ambiguous type constructor: " <> rtrName raw <> " (qualify with Mode.)")

buildTypeMapParams :: [ModeName] -> [RawTyVarDecl] -> Either Text [TyVar]
buildTypeMapParams sigModes decls = do
  if length sigModes /= length decls
    then Left "morphism: type mapping binder arity mismatch"
    else Right ()
  params <- mapM buildOne (zip sigModes decls)
  ensureDistinctTyVarNames "morphism: duplicate type mapping binders" params
  pure params
  where
    buildOne (mode, decl) =
      case rtvMode decl of
        Nothing -> Right TyVar { tvName = rtvName decl, tvMode = mode }
        Just modeName ->
          let explicit = ModeName modeName
          in if explicit == mode
              then Right TyVar { tvName = rtvName decl, tvMode = explicit }
              else Left "morphism: type mapping binder mode mismatch"

elabContext :: Doctrine -> ModeName -> [TyVar] -> RawPolyContext -> Either Text Context
elabContext doc expectedMode vars ctx = do
  tys <- mapM (elabTypeExpr doc vars) ctx
  let bad = filter (\ty -> typeMode ty /= expectedMode) tys
  if null bad
    then Right tys
    else Left "boundary type must match generator mode"

elabTypeExpr :: Doctrine -> [TyVar] -> RawPolyTypeExpr -> Either Text TypeExpr
elabTypeExpr doc vars expr =
  case expr of
    RPTVar name -> do
      v <- lookupTyVarByName vars name
      Right (TVar v)
    RPTCon rawRef args -> do
      ref <- resolveTypeRef doc rawRef
      sig <- lookupTypeSig doc ref
      let params = tsParams sig
      if length params /= length args
        then Left "type constructor arity mismatch"
        else do
          args' <- mapM (elabTypeExpr doc vars) args
          let argModes = map typeMode args'
          if and (zipWith (==) params argModes)
            then Right (TCon ref args')
            else Left "type constructor argument mode mismatch"

elabDiagExpr :: Doctrine -> ModeName -> [TyVar] -> RawDiagExpr -> Either Text Diagram
elabDiagExpr doc mode ruleVars expr =
  evalFresh (build expr)
  where
    rigid = S.fromList ruleVars
    build e =
      case e of
        RDId ctx -> do
          ctx' <- liftEither (elabContext doc mode ruleVars ctx)
          pure (idD mode ctx')
        RDGen name mArgs -> do
          gen <- liftEither (lookupGen doc mode (GenName name))
          let tyVars = gdTyVars gen
          renameSubst <- freshSubst tyVars
          let dom0 = applySubstCtx renameSubst (gdDom gen)
          let cod0 = applySubstCtx renameSubst (gdCod gen)
          (dom, cod) <- case mArgs of
            Nothing -> pure (dom0, cod0)
            Just args -> do
              args' <- mapM (liftEither . elabTypeExpr doc ruleVars) args
              if length args' /= length tyVars
                then liftEither (Left "generator type argument mismatch")
                else do
                  freshVars <- liftEither (extractFreshVars tyVars renameSubst)
                  case zipWith (\v t -> tvMode v == typeMode t) freshVars args' of
                    matches | and matches -> pure ()
                    _ -> liftEither (Left "generator type argument mode mismatch")
                  let subst = M.fromList (zip freshVars args')
                  pure (applySubstCtx subst dom0, applySubstCtx subst cod0)
          liftEither (genD mode dom cod (gdName gen))
        RDBox name innerExpr -> do
          inner <- build innerExpr
          dom <- liftEither (diagramDom inner)
          cod <- liftEither (diagramCod inner)
          let (ins, diag0) = allocPorts dom (emptyDiagram mode)
          let (outs, diag1) = allocPorts cod diag0
          diag2 <- liftEither (addEdgePayload (PBox (BoxName name) inner) ins outs diag1)
          let diag3 = diag2 { dIn = ins, dOut = outs }
          liftEither (validateDiagram diag3)
          pure diag3
        RDLoop innerExpr -> do
          inner <- build innerExpr
          case (dIn inner, dOut inner) of
            ([pIn], pOut:pOuts) -> do
              diag1 <- liftEither (mergePorts inner pOut pIn)
              let diag2 = diag1 { dIn = [], dOut = pOuts }
              liftEither (validateDiagram diag2)
              pure diag2
            _ -> liftEither (Left "loop: expected exactly one input and at least one output")
        RDComp a b -> do
          d1 <- build a
          d2 <- build b
          cod1 <- liftEither (diagramCod d1)
          dom2 <- liftEither (diagramDom d2)
          let free = S.union (freeTyVarsDiagram d1) (freeTyVarsDiagram d2)
          let flex = S.difference free rigid
          subst <- liftEither $
            case unifyCtxFlex flex cod1 dom2 of
              Left err -> Left ("diagram composition boundary mismatch: " <> err)
              Right s -> Right s
          let d1' = applySubstDiagram subst d1
          let d2' = applySubstDiagram subst d2
          liftEither (compD d2' d1')
        RDTensor a b -> do
          d1 <- build a
          d2 <- build b
          liftEither (tensorD d1 d2)

    allocPorts [] diag = ([], diag)
    allocPorts (ty:rest) diag =
      let (pid, diag1) = freshPort ty diag
          (pids, diag2) = allocPorts rest diag1
      in (pid:pids, diag2)

lookupGen :: Doctrine -> ModeName -> GenName -> Either Text GenDecl
lookupGen doc mode name =
  case M.lookup mode (dGens doc) >>= M.lookup name of
    Nothing -> Left "unknown generator"
    Just gd -> Right gd

unifyBoundary :: S.Set TyVar -> Context -> Context -> Diagram -> Either Text Diagram
unifyBoundary rigid dom cod diag = do
  domDiag <- diagramDom diag
  let flex0 = S.difference (freeTyVarsDiagram diag) rigid
  s1 <- unifyCtxFlex flex0 domDiag dom
  let diag1 = applySubstDiagram s1 diag
  codDiag <- diagramCod diag1
  let flex1 = S.difference (freeTyVarsDiagram diag1) rigid
  s2 <- unifyCtxFlex flex1 codDiag cod
  let diag2 = applySubstDiagram s2 diag1
  pure diag2

unifyCtxFlex :: S.Set TyVar -> Context -> Context -> Either Text Subst
unifyCtxFlex flex ctx1 ctx2
  | length ctx1 /= length ctx2 = Left "unifyCtxFlex: length mismatch"
  | otherwise = foldl step (Right M.empty) (zip ctx1 ctx2)
  where
    step acc (a, b) = do
      s <- acc
      let a' = applySubstTy s a
      let b' = applySubstTy s b
      s' <- unifyTyFlex flex a' b'
      pure (composeSubst s' s)

-- Freshening monad

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
        Just (TVar v') -> Right v'
        _ -> Left "internal error: expected fresh type variable"

freshVar :: TyVar -> Fresh (TyVar, TypeExpr)
freshVar v = do
  n <- freshInt
  let name = tvName v <> T.pack ("#" <> show n)
  let fresh = TyVar { tvName = name, tvMode = tvMode v }
  pure (v, TVar fresh)

freshInt :: Fresh Int
freshInt = Fresh (\n -> Right (n, n + 1))

liftEither :: Either Text a -> Fresh a
liftEither (Left err) = Fresh (\_ -> Left err)
liftEither (Right a) = pure a
