{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Doctrine
  ( GenDecl(..)
  , TypeSig(..)
  , Doctrine(..)
  , lookupTypeSig
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
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Attr
import Strat.Poly.Diagram
import Strat.Poly.Graph (validateDiagram, diagramIsoMatchWithVars)
import Strat.Poly.Cell2
import Strat.Poly.UnifyTy


data GenDecl = GenDecl
  { gdName :: GenName
  , gdMode :: ModeName
  , gdTyVars :: [TyVar]
  , gdDom :: Context
  , gdCod :: Context
  , gdAttrs :: [(AttrName, AttrSort)]
  } deriving (Eq, Show)

data Doctrine = Doctrine
  { dName :: Text
  , dModes :: ModeTheory
  , dAttrSorts :: M.Map AttrSort AttrSortDecl
  , dTypes :: M.Map ModeName (M.Map TypeName TypeSig)
  , dGens :: M.Map ModeName (M.Map GenName GenDecl)
  , dCells2 :: [Cell2]
  } deriving (Eq, Show)

data TypeSig = TypeSig
  { tsParams :: [ModeName]
  } deriving (Eq, Ord, Show)

cartMode :: ModeName
cartMode = ModeName "Cart"

validateDoctrine :: Doctrine -> Either Text ()
validateDoctrine doc = do
  checkModeTheory (dModes doc)
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

checkTypeTable :: Doctrine -> (ModeName, M.Map TypeName TypeSig) -> Either Text ()
checkTypeTable doc (mode, table)
  | M.member mode (mtModes (dModes doc)) = mapM_ checkSig (M.toList table)
  | otherwise = Left "validateDoctrine: types for unknown mode"
  where
    checkSig (_, sig)
      | any (`M.notMember` mtModes (dModes doc)) (tsParams sig) =
          Left "validateDoctrine: type signature uses unknown mode"
      | otherwise = Right ()

checkGenTable :: Doctrine -> (ModeName, M.Map GenName GenDecl) -> Either Text ()
checkGenTable doc (mode, gens)
  | M.member mode (mtModes (dModes doc)) = mapM_ (checkGen doc mode) (M.elems gens)
  | otherwise = Left "validateDoctrine: generators for unknown mode"

checkGen :: Doctrine -> ModeName -> GenDecl -> Either Text ()
checkGen doc mode gd
  | gdMode gd /= mode = Left "validateDoctrine: generator stored under wrong mode"
  | otherwise = do
      checkTyVarModes doc (gdTyVars gd)
      ensureDistinctTyVars ("validateDoctrine: duplicate generator tyvars in " <> renderGen (gdName gd)) (gdTyVars gd)
      checkContext doc mode (gdTyVars gd) (gdDom gd)
      checkContext doc mode (gdTyVars gd) (gdCod gd)
      checkGenAttrs doc gd

checkCell :: Doctrine -> Cell2 -> Either Text ()
checkCell doc cell = do
  validateDiagram (c2LHS cell)
  validateDiagram (c2RHS cell)
  ensureAttrVarNameSortsDiagram (freeAttrVarsDiagram (c2LHS cell))
  ensureAttrVarNameSortsDiagram (freeAttrVarsDiagram (c2RHS cell))
  if IM.size (dEdges (c2LHS cell)) <= 0
    then Left "validateDoctrine: empty LHS rules are disallowed (use an explicit marker generator if you need insertion)"
    else Right ()
  checkTyVarModes doc (c2TyVars cell)
  ensureDistinctTyVars ("validateDoctrine: duplicate cell tyvars in " <> c2Name cell) (c2TyVars cell)
  if dMode (c2LHS cell) /= dMode (c2RHS cell)
    then Left "validateDoctrine: cell has mode mismatch"
    else do
      ctxL <- diagramDom (c2LHS cell)
      ctxR <- diagramDom (c2RHS cell)
      _ <- unifyCtx (dModes doc) ctxL ctxR
      codL <- diagramCod (c2LHS cell)
      codR <- diagramCod (c2RHS cell)
      _ <- unifyCtx (dModes doc) codL codR
      let lhsVars = freeTyVarsDiagram (c2LHS cell)
      let rhsVars = freeTyVarsDiagram (c2RHS cell)
      if S.isSubsetOf rhsVars lhsVars
        then Right ()
        else Left "validateDoctrine: RHS introduces fresh type variables"
      let lhsAttrVars = freeAttrVarsDiagram (c2LHS cell)
      let rhsAttrVars = freeAttrVarsDiagram (c2RHS cell)
      if S.isSubsetOf rhsAttrVars lhsAttrVars
        then Right ()
        else Left "Cell RHS introduces fresh attribute variables"
      let vars = S.union lhsVars rhsVars
      let allowed = S.fromList (c2TyVars cell)
      if S.isSubsetOf vars allowed
        then Right ()
        else Left "validateDoctrine: cell uses undeclared type variables"

checkContext :: Doctrine -> ModeName -> [TyVar] -> Context -> Either Text ()
checkContext doc expectedMode tyvars ctx = mapM_ (checkBoundaryType doc expectedMode tyvars) ctx

checkBoundaryType :: Doctrine -> ModeName -> [TyVar] -> TypeExpr -> Either Text ()
checkBoundaryType doc expectedMode tyvars ty = do
  checkType doc tyvars ty
  if typeMode ty == expectedMode
    then Right ()
    else Left "validateDoctrine: generator boundary mode mismatch"

checkType :: Doctrine -> [TyVar] -> TypeExpr -> Either Text ()
checkType doc tyvars ty =
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
        else do
          mapM_ (checkType doc tyvars) args
          let argModes = map typeMode args
          if and (zipWith (==) params argModes)
            then Right ()
            else Left "validateDoctrine: type constructor argument mode mismatch"
    TMod _ inner -> do
      checkType doc tyvars inner
      _ <- normalizeTypeExpr (dModes doc) ty
      Right ()

ensureDistinctTyVars :: Text -> [TyVar] -> Either Text ()
ensureDistinctTyVars label vars =
  let names = map tvName vars
      set = S.fromList names
   in if S.size set == length names
        then Right ()
        else Left label

checkTyVarModes :: Doctrine -> [TyVar] -> Either Text ()
checkTyVarModes doc vars =
  if all (\v -> M.member (tvMode v) (mtModes (dModes doc))) vars
    then Right ()
    else Left "validateDoctrine: type variable has unknown mode"

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
      ensureDupShape dup
      Right dup

    requireDrop mode = do
      dropGen <- requireNamedGen mode "drop"
      ensureDropShape dropGen
      Right dropGen

    requireNamedGen mode name =
      case M.lookup mode (dGens doc) >>= M.lookup (GenName name) of
        Nothing -> Left ("validateDoctrine: mode " <> renderModeName mode <> " requires generator " <> name)
        Just gen -> Right gen

    ensureDupShape gen =
      case (gdTyVars gen, gdDom gen, gdCod gen) of
        ([v], [TVar v1], [TVar v2, TVar v3])
          | v == v1 && v == v2 && v == v3 -> Right ()
        _ -> Left "validateDoctrine: dup must have shape (a@M) : [a] -> [a,a]"

    ensureDropShape gen =
      case (gdTyVars gen, gdDom gen, gdCod gen) of
        ([v], [TVar v1], []) | v == v1 -> Right ()
        _ -> Left "validateDoctrine: drop must have shape (a@M) : [a] -> []"

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
      case diagramIsoMatchWithVars (dModes doc) (freeTyVarsDiagram expected) S.empty expected actual of
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

    renderModeName (ModeName t) = t
