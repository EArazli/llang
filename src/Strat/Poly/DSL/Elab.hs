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
import Strat.Poly.DSL.AST
import Strat.Poly.Doctrine
import Strat.Poly.Diagram
import Strat.Poly.ModeTheory
import Strat.Poly.Names
import Strat.Poly.TypeExpr
import Strat.Poly.UnifyTy
import Strat.Poly.RunSpec
import Strat.Poly.Morphism
import Strat.Frontend.RunSpec (RunShow(..))
import qualified Strat.Kernel.DSL.AST as KAST
import Strat.Kernel.DSL.AST (RawRunShow(..))
import Strat.Frontend.Env (ModuleEnv(..))
import Strat.Poly.Cell2 (Cell2(..))
import qualified Data.IntMap.Strict as IM
import Strat.Kernel.RewriteSystem (RewritePolicy(..))


elabPolyRun :: KAST.RawPolyRun -> Either Text PolyRunSpec
elabPolyRun raw = do
  let fuel = maybe 50 id (KAST.rprFuel raw)
  let flags = if null (KAST.rprShowFlags raw) then [ShowNormalized] else map toShow (KAST.rprShowFlags raw)
  let policyName = maybe "UseStructuralAsBidirectional" id (KAST.rprPolicy raw)
  policy <- parsePolicy policyName
  ensureShowFlags flags
  pure PolyRunSpec
    { prName = KAST.rprName raw
    , prDoctrine = KAST.rprDoctrine raw
    , prMode = KAST.rprMode raw
    , prSurface = KAST.rprSurface raw
    , prModel = KAST.rprModel raw
    , prPolicy = policy
    , prFuel = fuel
    , prShowFlags = flags
    , prExprText = KAST.rprExprText raw
    }
  where
    toShow s =
      case s of
        RawShowNormalized -> ShowNormalized
        RawShowInput -> ShowInput
        RawShowValue -> ShowValue
        RawShowCat -> ShowCat
    ensureShowFlags flags =
      if ShowCat `elem` flags
        then Left "polyrun: unsupported show flag (cat)"
        else if ShowValue `elem` flags && KAST.rprModel raw == Nothing
          then Left "polyrun: show value requires model"
          else Right ()

elabPolyMorphism :: ModuleEnv -> KAST.RawPolyMorphism -> Either Text Morphism
elabPolyMorphism env raw = do
  src <- lookupPolyDoctrine env (KAST.rpmSrc raw)
  tgt <- lookupPolyDoctrine env (KAST.rpmTgt raw)
  let policyName = maybe "UseStructuralAsBidirectional" id (KAST.rpmPolicy raw)
  policy <- parsePolicy policyName
  let fuel = maybe 50 id (KAST.rpmFuel raw)
  typeMap <- foldM (addTypeMap src tgt) M.empty [ t | KAST.RPMType t <- KAST.rpmItems raw ]
  genMap <- foldM (addGenMap src tgt) M.empty [ g | KAST.RPMGen g <- KAST.rpmItems raw ]
  ensureAllGenMapped src genMap
  let mor = Morphism
        { morName = KAST.rpmName raw
        , morSrc = src
        , morTgt = tgt
        , morTypeMap = typeMap
        , morGenMap = genMap
        , morPolicy = policy
        , morFuel = fuel
        }
  case checkMorphism mor of
    Left err -> Left ("polymorphism " <> KAST.rpmName raw <> ": " <> err)
    Right () -> Right mor
  where
    lookupPolyDoctrine env' name =
      case M.lookup name (mePolyDoctrines env') of
        Nothing -> Left ("Unknown polydoctrine: " <> name)
        Just doc -> Right doc
    addTypeMap src tgt mp decl = do
      let modeSrc = ModeName (KAST.rpmtSrcMode decl)
      let modeTgt = ModeName (KAST.rpmtTgtMode decl)
      if modeSrc /= modeTgt
        then Left "polymorphism: mode mapping not supported"
        else Right ()
      ensureMode src modeSrc
      ensureMode tgt modeSrc
      let name = TypeName (KAST.rpmtSrcType decl)
      arity <- case M.lookup modeSrc (dTypes src) >>= M.lookup name of
        Nothing -> Left "polymorphism: unknown source type"
        Just a -> Right a
      let vars = rawTypeVars (KAST.rpmtTgtType decl)
      tgtExpr <- elabTypeExpr tgt modeSrc (map TyVar vars) (KAST.rpmtTgtType decl)
      ensureTemplate arity tgtExpr
      let key = (modeSrc, name)
      if M.member key mp
        then Left "polymorphism: duplicate type mapping"
        else Right (M.insert key tgtExpr mp)
    addGenMap src tgt mp decl = do
      let mode = ModeName (KAST.rpmgMode decl)
      ensureMode src mode
      ensureMode tgt mode
      gen <- lookupGen src mode (GenName (KAST.rpmgSrcGen decl))
      let tyVars = gdTyVars gen
      diag <- elabDiagExpr tgt mode tyVars (KAST.rpmgRhs decl)
      let free = freeVars diag
      let allowed = S.fromList tyVars
      if S.isSubsetOf free allowed
        then Right ()
        else Left "polymorphism: generator mapping uses undeclared type variables"
      let key = (mode, gdName gen)
      if M.member key mp
        then Left "polymorphism: duplicate generator mapping"
        else Right (M.insert key diag mp)
    ensureTemplate arity expr =
      case expr of
        TCon _ params
          | length params == arity && all isVar params && distinct params -> Right ()
          | otherwise -> Left "polymorphism: type mapping must be a constructor with matching type variables"
        _ -> Left "polymorphism: type mapping must be a constructor with matching type variables"
    isVar (TVar _) = True
    isVar _ = False
    distinct params =
      let vars = [ v | TVar v <- params ]
      in length vars == length (S.fromList vars)
    rawTypeVars expr =
      S.toList (varsInRawType expr)
    varsInRawType expr =
      case expr of
        RPTVar name -> S.singleton name
        RPTCon _ args -> S.unions (map varsInRawType args)
    ensureAllGenMapped src mp = do
      let gens = [ (mode, gdName g) | (mode, table) <- M.toList (dGens src), g <- M.elems table ]
      case [ (m, g) | (m, g) <- gens, M.notMember (m, g) mp ] of
        [] -> Right ()
        _ -> Left "polymorphism: missing generator mapping"

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
      case M.lookup name (mePolyDoctrines env) of
        Nothing -> Left ("Unknown polydoctrine: " <> name)
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
      let arity = length (rptVars decl)
      let table = M.findWithDefault M.empty mode (dTypes doc)
      if M.member tname table
        then Left "duplicate type name"
        else do
          let table' = M.insert tname arity table
          let types' = M.insert mode table' (dTypes doc)
          pure doc { dTypes = types' }
    RPGen decl -> do
      let mode = ModeName (rpgMode decl)
      ensureMode doc mode
      let gname = GenName (rpgName decl)
      let vars = map TyVar (rpgVars decl)
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
      let ruleVars = map TyVar (rprVars decl)
      dom <- elabContext doc mode ruleVars (rprDom decl)
      cod <- elabContext doc mode ruleVars (rprCod decl)
      lhs <- withRule (elabDiagExpr doc mode ruleVars (rprLHS decl))
      rhs <- withRule (elabDiagExpr doc mode ruleVars (rprRHS decl))
      lhs' <- unifyBoundary dom cod lhs
      rhs' <- unifyBoundary dom cod rhs
      let free = S.union (freeVars lhs') (freeVars rhs')
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

elabContext :: Doctrine -> ModeName -> [TyVar] -> RawPolyContext -> Either Text Context
elabContext doc mode vars = mapM (elabTypeExpr doc mode vars)

elabTypeExpr :: Doctrine -> ModeName -> [TyVar] -> RawPolyTypeExpr -> Either Text TypeExpr
elabTypeExpr doc mode vars expr =
  case expr of
    RPTVar name ->
      let v = TyVar name
      in if v `elem` vars
        then Right (TVar v)
        else Left ("unknown type variable: " <> name)
    RPTCon name args -> do
      let tname = TypeName name
      let arity = M.lookup mode (dTypes doc) >>= M.lookup tname
      case arity of
        Nothing -> Left ("unknown type constructor: " <> name)
        Just a ->
          if a /= length args
            then Left ("type constructor arity mismatch: " <> name)
            else do
              args' <- mapM (elabTypeExpr doc mode vars) args
              pure (TCon tname args')

elabDiagExpr :: Doctrine -> ModeName -> [TyVar] -> RawDiagExpr -> Either Text Diagram
elabDiagExpr doc mode ruleVars expr =
  evalFresh (build expr)
  where
    build e =
      case e of
        RDId ctx -> do
          ctx' <- liftEither (elabContext doc mode ruleVars ctx)
          pure (idD mode ctx')
        RDGen name mArgs -> do
          gen <- liftEither (lookupGen doc mode (GenName name))
          let tyVars = gdTyVars gen
          subst <- case mArgs of
            Nothing -> freshSubst tyVars
            Just args -> do
              args' <- mapM (liftEither . elabTypeExpr doc mode ruleVars) args
              if length args' /= length tyVars
                then liftEither (Left "generator type argument mismatch")
                else pure (M.fromList (zip tyVars args'))
          let dom = applySubstCtx subst (gdDom gen)
          let cod = applySubstCtx subst (gdCod gen)
          liftEither (genD mode dom cod (gdName gen))
        RDComp a b -> do
          d1 <- build a
          d2 <- build b
          liftEither (compD d2 d1)
        RDTensor a b -> do
          d1 <- build a
          d2 <- build b
          liftEither (tensorD d1 d2)

lookupGen :: Doctrine -> ModeName -> GenName -> Either Text GenDecl
lookupGen doc mode name =
  case M.lookup mode (dGens doc) >>= M.lookup name of
    Nothing -> Left "unknown generator"
    Just gd -> Right gd

unifyBoundary :: Context -> Context -> Diagram -> Either Text Diagram
unifyBoundary dom cod diag = do
  domDiag <- diagramDom diag
  s1 <- unifyCtx domDiag dom
  let diag1 = applySubstDiagram s1 diag
  codDiag <- diagramCod diag1
  s2 <- unifyCtx codDiag cod
  let diag2 = applySubstDiagram s2 diag1
  pure diag2

freeVars :: Diagram -> S.Set TyVar
freeVars diag = S.fromList (concatMap varsInTy (IM.elems (dPortTy diag)))

varsInTy :: TypeExpr -> [TyVar]
varsInTy ty =
  case ty of
    TVar v -> [v]
    TCon _ args -> concatMap varsInTy args

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

freshVar :: TyVar -> Fresh (TyVar, TypeExpr)
freshVar (TyVar base) = do
  n <- freshInt
  let name = base <> T.pack ("#" <> show n)
  pure (TyVar base, TVar (TyVar name))

freshInt :: Fresh Int
freshInt = Fresh (\n -> Right (n, n + 1))

liftEither :: Either Text a -> Fresh a
liftEither (Left err) = Fresh (\_ -> Left err)
liftEither (Right a) = pure a
