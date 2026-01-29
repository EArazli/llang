{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Doctrine
  ( GenDecl(..)
  , Doctrine(..)
  , validateDoctrine
  , cartMode
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.IntMap.Strict as IM
import Strat.Poly.ModeTheory (ModeTheory(..), ModeName(..), ModDecl(..))
import Strat.Poly.TypeExpr
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Diagram
import Strat.Poly.Graph (validateDiagram)
import Strat.Poly.Cell2
import Strat.Poly.UnifyTy


data GenDecl = GenDecl
  { gdName   :: GenName
  , gdMode   :: ModeName
  , gdTyVars :: [TyVar]
  , gdDom    :: Context
  , gdCod    :: Context
  } deriving (Eq, Show)

data Doctrine = Doctrine
  { dName  :: Text
  , dModes :: ModeTheory
  , dTypes :: M.Map ModeName (M.Map TypeName Int)
  , dGens  :: M.Map ModeName (M.Map GenName GenDecl)
  , dCells2 :: [Cell2]
  } deriving (Eq, Show)

cartMode :: ModeName
cartMode = ModeName "Cart"

validateDoctrine :: Doctrine -> Either Text ()
validateDoctrine doc = do
  checkModeTheory (dModes doc)
  mapM_ (checkTypeTable doc) (M.toList (dTypes doc))
  mapM_ (checkGenTable doc) (M.toList (dGens doc))
  mapM_ (checkCell doc) (dCells2 doc)
  pure ()

checkModeTheory :: ModeTheory -> Either Text ()
checkModeTheory mt = do
  if S.null (mtModes mt)
    then Left "validateDoctrine: no modes declared"
    else Right ()
  mapM_ checkDecl (M.elems (mtDecls mt))
  where
    checkDecl decl
      | mdSrc decl `S.member` mtModes mt && mdTgt decl `S.member` mtModes mt = Right ()
      | otherwise = Left "validateDoctrine: modality uses unknown mode"

checkTypeTable :: Doctrine -> (ModeName, M.Map TypeName Int) -> Either Text ()
checkTypeTable doc (mode, table)
  | mode `S.member` mtModes (dModes doc) = mapM_ checkArity (M.toList table)
  | otherwise = Left "validateDoctrine: types for unknown mode"
  where
    checkArity (_, arity)
      | arity < 0 = Left "validateDoctrine: negative type arity"
      | otherwise = Right ()

checkGenTable :: Doctrine -> (ModeName, M.Map GenName GenDecl) -> Either Text ()
checkGenTable doc (mode, gens)
  | mode `S.member` mtModes (dModes doc) = mapM_ (checkGen doc mode) (M.elems gens)
  | otherwise = Left "validateDoctrine: generators for unknown mode"

checkGen :: Doctrine -> ModeName -> GenDecl -> Either Text ()
checkGen doc mode gd
  | gdMode gd /= mode = Left "validateDoctrine: generator stored under wrong mode"
  | otherwise = do
      ensureDistinctTyVars ("validateDoctrine: duplicate generator tyvars in " <> renderGen (gdName gd)) (gdTyVars gd)
      checkContext doc mode (gdTyVars gd) (gdDom gd)
      checkContext doc mode (gdTyVars gd) (gdCod gd)

checkCell :: Doctrine -> Cell2 -> Either Text ()
checkCell doc cell = do
  validateDiagram (c2LHS cell)
  validateDiagram (c2RHS cell)
  if IM.size (dEdges (c2LHS cell)) <= 0
    then Left "validateDoctrine: empty LHS rules are disallowed (use an explicit marker generator if you need insertion)"
    else Right ()
  ensureDistinctTyVars ("validateDoctrine: duplicate cell tyvars in " <> c2Name cell) (c2TyVars cell)
  if dMode (c2LHS cell) /= dMode (c2RHS cell)
    then Left "validateDoctrine: cell has mode mismatch"
    else do
      ctxL <- diagramDom (c2LHS cell)
      ctxR <- diagramDom (c2RHS cell)
      _ <- unifyCtx ctxL ctxR
      codL <- diagramCod (c2LHS cell)
      codR <- diagramCod (c2RHS cell)
      _ <- unifyCtx codL codR
      let lhsVars = freeTyVarsDiagram (c2LHS cell)
      let rhsVars = freeTyVarsDiagram (c2RHS cell)
      if S.isSubsetOf rhsVars lhsVars
        then Right ()
        else Left "validateDoctrine: RHS introduces fresh type variables"
      let vars = S.union lhsVars rhsVars
      let allowed = S.fromList (c2TyVars cell)
      if S.isSubsetOf vars allowed
        then Right ()
        else Left "validateDoctrine: cell uses undeclared type variables"

checkContext :: Doctrine -> ModeName -> [TyVar] -> Context -> Either Text ()
checkContext doc mode tyvars ctx = mapM_ (checkType doc mode tyvars) ctx

checkType :: Doctrine -> ModeName -> [TyVar] -> TypeExpr -> Either Text ()
checkType doc mode tyvars ty =
  case ty of
    TVar v ->
      if v `elem` tyvars
        then Right ()
        else Left "validateDoctrine: unknown type variable"
    TCon name args ->
      case M.lookup mode (dTypes doc) >>= M.lookup name of
        Nothing -> Left "validateDoctrine: unknown type constructor"
        Just arity ->
          if arity == length args
            then mapM_ (checkType doc mode tyvars) args
            else Left "validateDoctrine: type constructor arity mismatch"

ensureDistinctTyVars :: Text -> [TyVar] -> Either Text ()
ensureDistinctTyVars label vars =
  let set = S.fromList vars
  in if S.size set == length vars
    then Right ()
    else Left label

renderGen :: GenName -> Text
renderGen (GenName t) = t
