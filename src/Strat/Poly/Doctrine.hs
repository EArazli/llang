{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Doctrine
  ( InputShape(..)
  , BinderSig(..)
  , GenDecl(..)
  , ParamSig(..)
  , TypeSig(..)
  , Doctrine(..)
  , gdPlainDom
  , doctrineTypeTheory
  , lookupTypeSig
  , checkType
  , validateDoctrine
  , cartMode
  ) where

import Data.Text (Text)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.IntMap.Strict as IM
import qualified Data.List as L
import Strat.Poly.ModeTheory
import Strat.Poly.TypeExpr
import Strat.Poly.IndexTheory
import Strat.Poly.TypeTheory
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Attr
import Strat.Poly.Diagram
import Strat.Poly.Graph (validateDiagram, diagramIsoMatchWithVars)
import Strat.Poly.Cell2
import Strat.Poly.UnifyTy


data ParamSig
  = PS_Ty ModeName
  | PS_Ix TypeExpr
  deriving (Eq, Ord, Show)

newtype TypeSig = TypeSig
  { tsParams :: [ParamSig]
  } deriving (Eq, Ord, Show)

data BinderSig = BinderSig
  { bsIxCtx :: [TypeExpr]
  , bsDom :: Context
  , bsCod :: Context
  } deriving (Eq, Ord, Show)

data InputShape
  = InPort TypeExpr
  | InBinder BinderSig
  deriving (Eq, Ord, Show)

data GenDecl = GenDecl
  { gdName :: GenName
  , gdMode :: ModeName
  , gdTyVars :: [TyVar]
  , gdIxVars :: [IxVar]
  , gdDom :: [InputShape]
  , gdCod :: Context
  , gdAttrs :: [(AttrName, AttrSort)]
  } deriving (Eq, Show)

gdPlainDom :: GenDecl -> Context
gdPlainDom gd =
  [ ty
  | InPort ty <- gdDom gd
  ]

data Doctrine = Doctrine
  { dName :: Text
  , dModes :: ModeTheory
  , dIndexModes :: S.Set ModeName
  , dIxTheory :: M.Map ModeName IxTheory
  , dAttrSorts :: M.Map AttrSort AttrSortDecl
  , dTypes :: M.Map ModeName (M.Map TypeName TypeSig)
  , dGens :: M.Map ModeName (M.Map GenName GenDecl)
  , dCells2 :: [Cell2]
  } deriving (Eq, Show)

cartMode :: ModeName
cartMode = ModeName "Cart"

doctrineTypeTheory :: Doctrine -> TypeTheory
doctrineTypeTheory doc =
  TypeTheory
    { ttModes = dModes doc
    , ttIndex = dIxTheory doc
    , ttTypeParams =
        M.fromList
          [ (TypeRef mode tyName, map toTParam (tsParams sig))
          | (mode, typeTable) <- M.toList (dTypes doc)
          , (tyName, sig) <- M.toList typeTable
          ]
    , ttIxFuel = defaultIxFuel
    }
  where
    toTParam ps =
      case ps of
        PS_Ty m -> TPS_Ty m
        PS_Ix sortTy -> TPS_Ix sortTy

validateDoctrine :: Doctrine -> Either Text ()
validateDoctrine doc = do
  checkModeTheory (dModes doc)
  checkIndexModes doc
  mapM_ (checkIxTheoryTable doc) (M.toList (dIxTheory doc))
  mapM_ checkAttrSortDecl (M.toList (dAttrSorts doc))
  mapM_ (checkTypeTable doc) (M.toList (dTypes doc))
  mapM_ (checkGenTable doc) (M.toList (dGens doc))
  mapM_ (checkCell doc) (dCells2 doc)
  checkStructuralByDiscipline doc
  pure ()

lookupTypeSig :: Doctrine -> TypeRef -> Either Text TypeSig
lookupTypeSig doc ref =
  case M.lookup (trMode ref) (dTypes doc) of
    Nothing -> Left "lookupTypeSig: unknown mode for type"
    Just table ->
      case M.lookup (trName ref) table of
        Nothing -> Left "lookupTypeSig: unknown type constructor"
        Just sig -> Right sig

checkModeTheory :: ModeTheory -> Either Text ()
checkModeTheory = checkWellFormed

checkIndexModes :: Doctrine -> Either Text ()
checkIndexModes doc =
  if all (`M.member` mtModes (dModes doc)) (S.toList (dIndexModes doc))
    then Right ()
    else Left "validateDoctrine: index_mode references unknown mode"

checkIxTheoryTable :: Doctrine -> (ModeName, IxTheory) -> Either Text ()
checkIxTheoryTable doc (mode, ixTheory) = do
  if mode `S.member` dIndexModes doc
    then Right ()
    else Left "validateDoctrine: index theory declared for non-index mode"
  if M.member mode (mtModes (dModes doc))
    then Right ()
    else Left "validateDoctrine: index theory mode does not exist"
  mapM_ (checkIxFun mode) (M.toList (itFuns ixTheory))
  mapM_ (checkIxRule mode ixTheory) (itRules ixTheory)
  where
    tt = doctrineTypeTheory doc

    checkIxFun expectedMode (_fname, sig) = do
      mapM_ ensureIndexSort (ifArgs sig)
      ensureIndexSort (ifRes sig)
      resSort <- normalizeTypeDeep tt (ifRes sig)
      if typeMode resSort == expectedMode
        then Right ()
        else Left "validateDoctrine: index_fun result mode mismatch"

    checkIxRule expectedMode theory rule = do
      mapM_ (ensureIndexSort . ixvSort) (irVars rule)
      lhsSort <- inferIxSortRule tt theory (M.fromList [(ixvName v, ixvSort v) | v <- irVars rule]) (irLHS rule)
      rhsSort <- inferIxSortRule tt theory (M.fromList [(ixvName v, ixvSort v) | v <- irVars rule]) (irRHS rule)
      lhsSort' <- normalizeTypeDeep tt lhsSort
      rhsSort' <- normalizeTypeDeep tt rhsSort
      if lhsSort' /= rhsSort'
        then Left "validateDoctrine: index_rule lhs/rhs sort mismatch"
        else Right ()
      if typeMode lhsSort' == expectedMode
        then Right ()
        else Left "validateDoctrine: index_rule result mode mismatch"
      checkIxTerm doc [] (irVars rule) [] lhsSort' (irLHS rule)
      checkIxTerm doc [] (irVars rule) [] lhsSort' (irRHS rule)

    ensureIndexSort sortTy =
      if typeMode sortTy `S.member` dIndexModes doc
        then checkType doc [] [] [] sortTy
        else Left "validateDoctrine: index sort must live in an index_mode"

checkTypeTable :: Doctrine -> (ModeName, M.Map TypeName TypeSig) -> Either Text ()
checkTypeTable doc (mode, table)
  | M.member mode (mtModes (dModes doc)) = mapM_ checkSig (M.toList table)
  | otherwise = Left "validateDoctrine: types for unknown mode"
  where
    checkSig (_name, sig) = mapM_ checkParam (tsParams sig)
    checkParam ps =
      case ps of
        PS_Ty m ->
          if M.member m (mtModes (dModes doc))
            then Right ()
            else Left "validateDoctrine: type signature uses unknown mode"
        PS_Ix sortTy -> do
          checkType doc [] [] [] sortTy
          if typeMode sortTy `S.member` dIndexModes doc
            then Right ()
            else Left "validateDoctrine: PS_Ix sort must be in an index mode"

checkGenTable :: Doctrine -> (ModeName, M.Map GenName GenDecl) -> Either Text ()
checkGenTable doc (mode, gens)
  | M.member mode (mtModes (dModes doc)) = mapM_ (checkGen doc mode) (M.elems gens)
  | otherwise = Left "validateDoctrine: generators for unknown mode"

checkGen :: Doctrine -> ModeName -> GenDecl -> Either Text ()
checkGen doc mode gd
  | gdMode gd /= mode = Left "validateDoctrine: generator stored under wrong mode"
  | otherwise = do
      checkTyVarModes doc (gdTyVars gd)
      checkIxVarModes doc (gdIxVars gd)
      ensureDistinctTyVars ("validateDoctrine: duplicate generator tyvars in " <> renderGen (gdName gd)) (gdTyVars gd)
      ensureDistinctIxVars ("validateDoctrine: duplicate generator ixvars in " <> renderGen (gdName gd)) (gdIxVars gd)
      mapM_ (checkInputShape doc mode (gdTyVars gd) (gdIxVars gd)) (gdDom gd)
      checkContext doc mode (gdTyVars gd) (gdIxVars gd) [] (gdCod gd)
      checkGenAttrs doc gd

checkInputShape :: Doctrine -> ModeName -> [TyVar] -> [IxVar] -> InputShape -> Either Text ()
checkInputShape doc expectedMode tyvars ixvars shape =
  case shape of
    InPort ty -> checkBoundaryType doc expectedMode tyvars ixvars [] ty
    InBinder bs -> checkBinderSig doc expectedMode tyvars ixvars bs

checkBinderSig :: Doctrine -> ModeName -> [TyVar] -> [IxVar] -> BinderSig -> Either Text ()
checkBinderSig doc expectedMode tyvars ixvars bs = do
  checkIxCtxTele (bsIxCtx bs)
  checkContext doc expectedMode tyvars ixvars (bsIxCtx bs) (bsDom bs)
  checkContext doc expectedMode tyvars ixvars (bsIxCtx bs) (bsCod bs)
  where
    checkIxCtxTele ctx =
      mapM_ checkAt (zip [0 :: Int ..] ctx)

    checkAt (i, ty) = do
      checkType doc tyvars ixvars (take i (bsIxCtx bs)) ty
      if typeMode ty `S.member` dIndexModes doc
        then Right ()
        else Left "validateDoctrine: binder index context sort must be in an index mode"

checkCell :: Doctrine -> Cell2 -> Either Text ()
checkCell doc cell = do
  validateDiagram (c2LHS cell)
  validateDiagram (c2RHS cell)
  ensureAttrVarNameSortsDiagram (freeAttrVarsDiagram (c2LHS cell))
  ensureAttrVarNameSortsDiagram (freeAttrVarsDiagram (c2RHS cell))
  if S.null (spliceMetaVarsDiagram (c2LHS cell))
    then Right ()
    else Left "validateDoctrine: splice nodes are not allowed in rule LHS"
  if IM.size (dEdges (c2LHS cell)) <= 0
    then Left "validateDoctrine: empty LHS rules are disallowed (use an explicit marker generator if you need insertion)"
    else Right ()
  checkTyVarModes doc (c2TyVars cell)
  checkIxVarModes doc (c2IxVars cell)
  ensureDistinctTyVars ("validateDoctrine: duplicate cell tyvars in " <> c2Name cell) (c2TyVars cell)
  ensureDistinctIxVars ("validateDoctrine: duplicate cell ixvars in " <> c2Name cell) (c2IxVars cell)
  if dMode (c2LHS cell) /= dMode (c2RHS cell)
    then Left "validateDoctrine: cell has mode mismatch"
    else if dIxCtx (c2LHS cell) /= dIxCtx (c2RHS cell)
      then Left "validateDoctrine: cell has index-context mismatch"
    else do
      ctxL <- diagramDom (c2LHS cell)
      ctxR <- diagramDom (c2RHS cell)
      let tt = doctrineTypeTheory doc
      let tyFlexDom = S.unions (map freeTyVarsTypeLocal (ctxL <> ctxR))
      let ixFlexDom = S.unions (map freeIxVarsType (ctxL <> ctxR))
      _ <- unifyCtx tt [] tyFlexDom ixFlexDom ctxL ctxR
      codL <- diagramCod (c2LHS cell)
      codR <- diagramCod (c2RHS cell)
      let tyFlexCod = S.unions (map freeTyVarsTypeLocal (codL <> codR))
      let ixFlexCod = S.unions (map freeIxVarsType (codL <> codR))
      _ <- unifyCtx tt [] tyFlexCod ixFlexCod codL codR
      let lhsVars = freeTyVarsDiagram (c2LHS cell)
      let rhsVars = freeTyVarsDiagram (c2RHS cell)
      let declaredTy = S.fromList (c2TyVars cell)
      if S.isSubsetOf rhsVars (S.union lhsVars declaredTy)
        then Right ()
        else Left "validateDoctrine: RHS introduces fresh type variables"
      let lhsIxVars = freeIxVarsDiagram (c2LHS cell)
      let rhsIxVars = freeIxVarsDiagram (c2RHS cell)
      let declaredIx = S.fromList (c2IxVars cell)
      if S.isSubsetOf rhsIxVars (S.union lhsIxVars declaredIx)
        then Right ()
        else Left "validateDoctrine: RHS introduces fresh index variables"
      let lhsAttrVars = freeAttrVarsDiagram (c2LHS cell)
      let rhsAttrVars = freeAttrVarsDiagram (c2RHS cell)
      if S.isSubsetOf rhsAttrVars lhsAttrVars
        then Right ()
        else Left "Cell RHS introduces fresh attribute variables"
      let vars = S.union lhsVars rhsVars
      if S.isSubsetOf vars declaredTy
        then Right ()
        else Left "validateDoctrine: cell uses undeclared type variables"
      let ixVars = S.union lhsIxVars rhsIxVars
      if S.isSubsetOf ixVars declaredIx
        then Right ()
        else Left "validateDoctrine: cell uses undeclared index variables"
      let lhsCapturedMetas = binderArgMetaVarsDiagram (c2LHS cell)
      let rhsReferencedMetas = S.union (binderArgMetaVarsDiagram (c2RHS cell)) (spliceMetaVarsDiagram (c2RHS cell))
      if S.isSubsetOf rhsReferencedMetas lhsCapturedMetas
        then Right ()
        else Left "validateDoctrine: RHS references binder metas not captured by LHS binder arguments"

checkContext :: Doctrine -> ModeName -> [TyVar] -> [IxVar] -> [TypeExpr] -> Context -> Either Text ()
checkContext doc expectedMode tyvars ixvars ixCtx ctx = mapM_ (checkBoundaryType doc expectedMode tyvars ixvars ixCtx) ctx

checkBoundaryType :: Doctrine -> ModeName -> [TyVar] -> [IxVar] -> [TypeExpr] -> TypeExpr -> Either Text ()
checkBoundaryType doc expectedMode tyvars ixvars ixCtx ty = do
  checkType doc tyvars ixvars ixCtx ty
  if typeMode ty == expectedMode
    then Right ()
    else Left "validateDoctrine: generator boundary mode mismatch"

checkType :: Doctrine -> [TyVar] -> [IxVar] -> [TypeExpr] -> TypeExpr -> Either Text ()
checkType doc tyvars ixvars ixCtx ty =
  case ty of
    TVar v ->
      if v `elem` tyvars
        then
          if M.member (tvMode v) (mtModes (dModes doc))
            then Right ()
            else Left "validateDoctrine: type variable has unknown mode"
        else Left "validateDoctrine: unknown type variable"
    TCon ref args -> do
      sig <- lookupTypeSig doc ref
      let params = tsParams sig
      if length params /= length args
        then Left "validateDoctrine: type constructor arity mismatch"
        else mapM_ (checkArg ref) (zip params args)
    TMod _ inner -> do
      checkType doc tyvars ixvars ixCtx inner
      _ <- normalizeTypeExpr (dModes doc) ty
      Right ()
  where
    checkArg _ (PS_Ty m, TAType argTy) = do
      checkType doc tyvars ixvars ixCtx argTy
      if typeMode argTy == m
        then Right ()
        else Left "validateDoctrine: type constructor argument mode mismatch"
    checkArg _ (PS_Ix sortTy, TAIndex ixTerm) = do
      checkType doc tyvars ixvars ixCtx sortTy
      checkIxTerm doc tyvars ixvars ixCtx sortTy ixTerm
    checkArg _ _ = Left "validateDoctrine: type argument kind mismatch"

checkIxTerm :: Doctrine -> [TyVar] -> [IxVar] -> [TypeExpr] -> TypeExpr -> IxTerm -> Either Text ()
checkIxTerm doc tyvars ixvars ixCtx expectedSort tm =
  case tm of
    IXVar v -> do
      if v `elem` ixvars
        then Right ()
        else Left "validateDoctrine: unknown index variable"
      checkType doc tyvars ixvars ixCtx (ixvSort v)
      sameSort <- sortDefEq (ixvSort v) expectedSort
      if sameSort
        then Right ()
        else Left "validateDoctrine: index variable sort mismatch"
    IXBound i ->
      if i < length ixCtx
        then do
          sameSort <- sortDefEq (ixCtx !! i) expectedSort
          if sameSort
            then Right ()
            else Left "validateDoctrine: IXBound sort mismatch"
        else Left "validateDoctrine: IXBound out of scope"
    IXFun fname args -> do
      modeTheory <-
        case M.lookup (typeMode expectedSort) (dIxTheory doc) of
          Nothing -> Left "validateDoctrine: missing index theory for expected sort mode"
          Just th -> Right th
      sig <-
        case M.lookup fname (itFuns modeTheory) of
          Nothing -> Left "validateDoctrine: unknown index function"
          Just s -> Right s
      if length (ifArgs sig) /= length args
        then Left "validateDoctrine: index function arity mismatch"
        else mapM_ (uncurry (checkIxTerm doc tyvars ixvars ixCtx)) (zip (ifArgs sig) args)
      sameSort <- sortDefEq (ifRes sig) expectedSort
      if sameSort
        then Right ()
        else Left "validateDoctrine: index function result sort mismatch"
  where
    tt = doctrineTypeTheory doc

    sortDefEq lhs rhs = do
      lhs' <- normalizeTypeDeep tt lhs
      rhs' <- normalizeTypeDeep tt rhs
      pure (lhs' == rhs')

ensureDistinctTyVars :: Text -> [TyVar] -> Either Text ()
ensureDistinctTyVars label vars =
  let names = map tvName vars
      set = S.fromList names
   in if S.size set == length names
        then Right ()
        else Left label

ensureDistinctIxVars :: Text -> [IxVar] -> Either Text ()
ensureDistinctIxVars label vars =
  let names = map ixvName vars
      set = S.fromList names
   in if S.size set == length names
        then Right ()
        else Left label

checkTyVarModes :: Doctrine -> [TyVar] -> Either Text ()
checkTyVarModes doc vars =
  if all (\v -> M.member (tvMode v) (mtModes (dModes doc))) vars
    then Right ()
    else Left "validateDoctrine: type variable has unknown mode"

checkIxVarModes :: Doctrine -> [IxVar] -> Either Text ()
checkIxVarModes doc vars =
  mapM_ checkOne vars
  where
    checkOne v = do
      checkType doc [] vars [] (ixvSort v)
      if typeMode (ixvSort v) `S.member` dIndexModes doc
        then Right ()
        else Left "validateDoctrine: index variable sort must be in an index mode"

checkAttrSortDecl :: (AttrSort, AttrSortDecl) -> Either Text ()
checkAttrSortDecl (name, decl) =
  if asName decl == name
    then Right ()
    else Left "validateDoctrine: attribute sort declaration mismatch"

checkGenAttrs :: Doctrine -> GenDecl -> Either Text ()
checkGenAttrs doc gd = do
  ensureDistinct ("validateDoctrine: duplicate generator attribute names in " <> renderGen (gdName gd)) (map fst (gdAttrs gd))
  mapM_ ensureSortExists (gdAttrs gd)
  where
    ensureSortExists (_, sortName) =
      if M.member sortName (dAttrSorts doc)
        then Right ()
        else Left ("validateDoctrine: unknown attribute sort in generator " <> renderGen (gdName gd))

ensureDistinct :: Ord a => Text -> [a] -> Either Text ()
ensureDistinct label xs =
  if length (L.nub xs) == length xs
    then Right ()
    else Left label

renderGen :: GenName -> Text
renderGen (GenName t) = t

renderModeName :: ModeName -> Text
renderModeName (ModeName t) = t

checkStructuralByDiscipline :: Doctrine -> Either Text ()
checkStructuralByDiscipline doc =
  mapM_ checkOneMode (M.toList (mtModes (dModes doc)))
  where
    checkOneMode (mode, info) =
      case miDiscipline info of
        Linear -> Right ()
        Affine -> do
          _ <- requireDrop mode
          Right ()
        Relevant -> do
          _ <- requireDup mode
          requireCoassoc mode
        Cartesian -> do
          _ <- requireDup mode
          _ <- requireDrop mode
          requireCoassoc mode
          requireCounitLeft mode
          requireCounitRight mode

    requireDup mode = do
      dup <- requireNamedGen mode "dup"
      ensureDupShape mode dup
      Right dup

    requireDrop mode = do
      dropGen <- requireNamedGen mode "drop"
      ensureDropShape mode dropGen
      Right dropGen

    requireNamedGen mode name =
      case M.lookup mode (dGens doc) >>= M.lookup (GenName name) of
        Nothing -> Left ("validateDoctrine: mode " <> renderModeName mode <> " requires generator " <> name)
        Just gen -> Right gen

    ensureDupShape mode gen =
      if not (null (gdAttrs gen))
        then Left ("dup in mode " <> renderModeName mode <> " must not declare attributes")
        else
          case (gdTyVars gen, gdDom gen, gdCod gen) of
            ([v], [InPort (TVar v1)], [TVar v2, TVar v3])
              | v == v1 && v == v2 && v == v3 -> Right ()
            _ -> Left "validateDoctrine: dup must have shape (a@M) : [a] -> [a,a] (no binder slots)"

    ensureDropShape mode gen =
      if not (null (gdAttrs gen))
        then Left ("drop in mode " <> renderModeName mode <> " must not declare attributes")
        else
          case (gdTyVars gen, gdDom gen, gdCod gen) of
            ([v], [InPort (TVar v1)], []) | v == v1 -> Right ()
            _ -> Left "validateDoctrine: drop must have shape (a@M) : [a] -> [] (no binder slots)"

    requireCoassoc mode = do
      (lhs, rhs) <- lawCoassoc mode
      requireLaw "coassociativity" lhs rhs

    requireCounitLeft mode = do
      (lhs, rhs) <- lawCounitLeft mode
      requireLaw "counit-left" lhs rhs

    requireCounitRight mode = do
      (lhs, rhs) <- lawCounitRight mode
      requireLaw "counit-right" lhs rhs

    requireLaw label expectedL expectedR =
      case filter (cellSatisfies expectedL expectedR) (dCells2 doc) of
        [] -> Left ("validateDoctrine: missing structural law " <> label)
        _ -> Right ()

    cellSatisfies expectedL expectedR cell =
      let lhs = c2LHS cell
          rhs = c2RHS cell
       in (matches expectedL lhs && matches expectedR rhs)
            || (matches expectedR lhs && matches expectedL rhs)

    matches expected actual =
      case
        diagramIsoMatchWithVars
          (doctrineTypeTheory doc)
          (freeTyVarsDiagram expected)
          (freeIxVarsDiagram expected)
          S.empty
          expected
          actual
        of
        Right (_:_) -> True
        _ -> False

    lawCoassoc mode = do
      a <- lawTyVar mode
      dup <- genD mode [TVar a] [TVar a, TVar a] (GenName "dup")
      ida <- pure (idD mode [TVar a])
      lhsTail <- tensorD dup ida
      rhsTail <- tensorD ida dup
      lhs <- compD (dModes doc) lhsTail dup
      rhs <- compD (dModes doc) rhsTail dup
      Right (lhs, rhs)

    lawCounitLeft mode = do
      a <- lawTyVar mode
      dup <- genD mode [TVar a] [TVar a, TVar a] (GenName "dup")
      dropA <- genD mode [TVar a] [] (GenName "drop")
      ida <- pure (idD mode [TVar a])
      tailL <- tensorD dropA ida
      lhs <- compD (dModes doc) tailL dup
      let rhs = idD mode [TVar a]
      Right (lhs, rhs)

    lawCounitRight mode = do
      a <- lawTyVar mode
      dup <- genD mode [TVar a] [TVar a, TVar a] (GenName "dup")
      dropA <- genD mode [TVar a] [] (GenName "drop")
      ida <- pure (idD mode [TVar a])
      tailL <- tensorD ida dropA
      lhs <- compD (dModes doc) tailL dup
      let rhs = idD mode [TVar a]
      Right (lhs, rhs)

    lawTyVar mode =
      Right TyVar { tvName = "a", tvMode = mode }

inferIxSortRule :: TypeTheory -> IxTheory -> M.Map Text TypeExpr -> IxTerm -> Either Text TypeExpr
inferIxSortRule tt theory varSorts tm =
  case tm of
    IXVar v -> do
      ty <-
        case M.lookup (ixvName v) varSorts of
          Nothing -> Left "validateDoctrine: index_rule uses undeclared index variable"
          Just sortTy -> Right sortTy
      varSort' <- normalizeTypeDeep tt (ixvSort v)
      ty' <- normalizeTypeDeep tt ty
      if varSort' == ty'
        then Right ty
        else Left "validateDoctrine: index_rule variable sort mismatch"
    IXBound _ ->
      Left "validateDoctrine: index_rule cannot use bound indices"
    IXFun fname args ->
      case M.lookup fname (itFuns theory) of
        Nothing -> Left "validateDoctrine: index_rule references unknown index_fun"
        Just sig -> do
          if length (ifArgs sig) /= length args
            then Left "validateDoctrine: index_rule function arity mismatch"
            else Right (ifRes sig)

freeTyVarsTypeLocal :: TypeExpr -> S.Set TyVar
freeTyVarsTypeLocal ty =
  case ty of
    TVar v -> S.singleton v
    TCon _ args -> S.unions (map freeArg args)
    TMod _ inner -> freeTyVarsTypeLocal inner
  where
    freeArg arg =
      case arg of
        TAType t -> freeTyVarsTypeLocal t
        TAIndex ix -> S.unions [ freeTyVarsTypeLocal (ixvSort v) | v <- S.toList (freeIxVarsIx ix) ]
