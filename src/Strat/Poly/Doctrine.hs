{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Doctrine
  ( InputShape(..)
  , BinderSig(..)
  , GenDecl(..)
  , ModAction(..)
  , ObligationDecl(..)
  , ParamSig(..)
  , TypeSig(..)
  , Doctrine(..)
  , gdPlainDom
  , doctrineTypeTheory
  , lookupTypeSig
  , checkType
  , validateDoctrine
  , modeIsAcyclic
  ) where

import Data.Text (Text)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.IntMap.Strict as IM
import qualified Data.List as L
import qualified Data.Text as T
import Strat.Poly.ModeTheory
import Strat.Poly.TypeExpr
import Strat.Poly.TypeTheory
  ( TypeTheory(..)
  , TypeParamSig(..)
  , TmFunSig(..)
  , TmRule(..)
  , defaultTmFuel
  )
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Attr
import Strat.Poly.Diagram
import Strat.Poly.Graph (validateDiagram, Edge(..), EdgePayload(..), unPortId)
import Strat.Poly.Cell2
import Strat.Poly.UnifyTy (unifyCtx)
import Strat.Common.Rules (RewritePolicy(..), RuleClass(..), Orientation(..))
import Strat.Poly.TypeNormalize (termToDiagram, validateTermDiagram)


data ParamSig
  = PS_Ty ModeName
  | PS_Tm TypeExpr
  deriving (Eq, Ord, Show)

newtype TypeSig = TypeSig
  { tsParams :: [ParamSig]
  } deriving (Eq, Ord, Show)

data BinderSig = BinderSig
  { bsTmCtx :: [TypeExpr]
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
  , gdTmVars :: [TmVar]
  , gdDom :: [InputShape]
  , gdCod :: Context
  , gdAttrs :: [(AttrName, AttrSort)]
  } deriving (Eq, Show)

data ModAction = ModAction
  { maMod :: ModName
  , maGenMap :: M.Map (ModeName, GenName) Diagram
  , maPolicy :: RewritePolicy
  , maFuel :: Int
  } deriving (Eq, Show)

data ObligationDecl = ObligationDecl
  { obName :: Text
  , obTyVars :: [TyVar]
  , obTmVars :: [TmVar]
  , obLHS :: Diagram
  , obRHS :: Diagram
  , obPolicy :: RewritePolicy
  , obFuel :: Int
  } deriving (Eq, Show)

gdPlainDom :: GenDecl -> Context
gdPlainDom gd =
  [ ty
  | InPort ty <- gdDom gd
  ]

data Doctrine = Doctrine
  { dName :: Text
  , dModes :: ModeTheory
  , dAcyclicModes :: S.Set ModeName
  , dAttrSorts :: M.Map AttrSort AttrSortDecl
  , dTypes :: M.Map ModeName (M.Map TypeName TypeSig)
  , dGens :: M.Map ModeName (M.Map GenName GenDecl)
  , dCells2 :: [Cell2]
  , dActions :: M.Map ModName ModAction
  , dObligations :: [ObligationDecl]
  } deriving (Eq, Show)

doctrineTypeTheory :: Doctrine -> TypeTheory
doctrineTypeTheory doc =
  let tmFuns = derivedTmFuns doc
      tmRules = derivedTmRules doc tmFuns
   in
  TypeTheory
    { ttModes = dModes doc
    , ttTypeParams =
        M.fromList
          [ (TypeRef mode tyName, map toTParam (tsParams sig))
          | (mode, typeTable) <- M.toList (dTypes doc)
          , (tyName, sig) <- M.toList typeTable
          ]
    , ttTmFuns = tmFuns
    , ttTmRules = tmRules
    , ttTmFuel = defaultTmFuel
    , ttTmPolicy = UseOnlyComputationalLR
    }
  where
    toTParam ps =
      case ps of
        PS_Ty m -> TPS_Ty m
        PS_Tm sortTy -> TPS_Tm sortTy

derivedTmFuns :: Doctrine -> M.Map ModeName (M.Map TmFunName TmFunSig)
derivedTmFuns doc =
  M.fromList
    [ (mode, funs)
    | (mode, table) <- M.toList (dGens doc)
    , let funs =
            M.fromList
              [ (TmFunName gName, TmFunSig { tfsArgs = [ ty | InPort ty <- gdDom gd ], tfsRes = res })
              | gd <- M.elems table
              , let GenName gName = gdName gd
              , null (gdTyVars gd)
              , null (gdTmVars gd)
              , null (gdAttrs gd)
              , all isPort (gdDom gd)
              , [res] <- [gdCod gd]
              ]
    , not (M.null funs)
    ]
  where
    isPort sh =
      case sh of
        InPort _ -> True
        InBinder _ -> False

derivedTmRules :: Doctrine -> M.Map ModeName (M.Map TmFunName TmFunSig) -> M.Map ModeName [TmRule]
derivedTmRules doc tmFuns =
  M.fromListWith (<>)
    [ (mode, [rule])
    | cell <- dCells2 doc
    , c2Class cell == Computational
    , (lhs, rhs) <- oriented cell
    , let mode = dMode lhs
    , Just funs <- [M.lookup mode tmFuns]
    , Just rule <- [cellPairToTmRule funs lhs rhs]
    ]
  where
    oriented cell =
      case c2Orient cell of
        LR -> [(c2LHS cell, c2RHS cell)]
        RL -> [(c2RHS cell, c2LHS cell)]
        Bidirectional -> [(c2LHS cell, c2RHS cell), (c2RHS cell, c2LHS cell)]
        Unoriented -> []

cellPairToTmRule :: M.Map TmFunName TmFunSig -> Diagram -> Diagram -> Maybe TmRule
cellPairToTmRule funs lhs rhs = do
  vars <- mkInputVars lhs
  ensureTermDiagram lhs
  ensureTermDiagram rhs
  ensureRuleFunSigs lhs
  ensureRuleFunSigs rhs
  pure TmRule { trVars = vars, trLHS = TermDiagram lhs, trRHS = TermDiagram rhs }
  where
    ensureTermDiagram d = either (const Nothing) (const (Just ())) (validateTermDiagram d)
    ensureRuleFunSigs d = mapM_ checkEdge (IM.elems (dEdges d))
    checkEdge edge =
      case ePayload edge of
        PGen (GenName gName) attrs bargs
          | M.null attrs && null bargs -> do
              sig <- M.lookup (TmFunName gName) funs
              if length (tfsArgs sig) == length (eIns edge) && length (eOuts edge) == 1
                then Just ()
                else Nothing
        PTmMeta _ -> Just ()
        _ -> Nothing

mkInputVars :: Diagram -> Maybe [TmVar]
mkInputVars diag =
  mapM mkOne (zip [0 :: Int ..] (dIn diag))
  where
    mkOne (i, pid) = do
      sortTy <- IM.lookup (unPortId pid) (dPortTy diag)
      pure TmVar { tmvName = "_x" <> T.pack (show i), tmvSort = sortTy, tmvScope = 0 }

validateDoctrine :: Doctrine -> Either Text ()
validateDoctrine doc = do
  checkModeTheory (dModes doc)
  if all (`M.member` mtModes (dModes doc)) (S.toList (dAcyclicModes doc))
    then Right ()
    else Left "validateDoctrine: acyclic mode references unknown mode"
  mapM_ checkAttrSortDecl (M.toList (dAttrSorts doc))
  mapM_ (checkTypeTable doc) (M.toList (dTypes doc))
  mapM_ (checkGenTable doc) (M.toList (dGens doc))
  mapM_ (checkCell doc) (dCells2 doc)
  mapM_ (checkAction doc) (M.toList (dActions doc))
  mapM_ checkObligation (dObligations doc)
  pure ()

modeIsAcyclic :: Doctrine -> ModeName -> Bool
modeIsAcyclic doc mode = mode `S.member` dAcyclicModes doc

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
    checkSig (_name, sig) = mapM_ checkParam (tsParams sig)
    checkParam ps =
      case ps of
        PS_Ty m ->
          if M.member m (mtModes (dModes doc))
            then Right ()
            else Left "validateDoctrine: type signature uses unknown mode"
        PS_Tm sortTy -> do
          checkType doc [] [] [] sortTy
          Right ()

checkGenTable :: Doctrine -> (ModeName, M.Map GenName GenDecl) -> Either Text ()
checkGenTable doc (mode, gens)
  | M.member mode (mtModes (dModes doc)) = mapM_ (checkGen doc mode) (M.elems gens)
  | otherwise = Left "validateDoctrine: generators for unknown mode"

checkGen :: Doctrine -> ModeName -> GenDecl -> Either Text ()
checkGen doc mode gd
  | gdMode gd /= mode = Left "validateDoctrine: generator stored under wrong mode"
  | otherwise = do
      checkTyVarModes doc (gdTyVars gd)
      checkTmVarModes doc (gdTmVars gd)
      ensureDistinctTyVars ("validateDoctrine: duplicate generator tyvars in " <> renderGen (gdName gd)) (gdTyVars gd)
      ensureDistinctTmVars ("validateDoctrine: duplicate generator term vars in " <> renderGen (gdName gd)) (gdTmVars gd)
      mapM_ (checkInputShape doc mode (gdTyVars gd) (gdTmVars gd)) (gdDom gd)
      checkContext doc mode (gdTyVars gd) (gdTmVars gd) [] (gdCod gd)
      checkGenAttrs doc gd

checkInputShape :: Doctrine -> ModeName -> [TyVar] -> [TmVar] -> InputShape -> Either Text ()
checkInputShape doc expectedMode tyvars tmvars shape =
  case shape of
    InPort ty -> checkBoundaryType doc expectedMode tyvars tmvars [] ty
    InBinder bs -> checkBinderSig doc expectedMode tyvars tmvars bs

checkBinderSig :: Doctrine -> ModeName -> [TyVar] -> [TmVar] -> BinderSig -> Either Text ()
checkBinderSig doc expectedMode tyvars tmvars bs = do
  checkTmCtxTele (bsTmCtx bs)
  checkContext doc expectedMode tyvars tmvars (bsTmCtx bs) (bsDom bs)
  checkContext doc expectedMode tyvars tmvars (bsTmCtx bs) (bsCod bs)
  where
    checkTmCtxTele ctx =
      mapM_ checkAt (zip [0 :: Int ..] ctx)

    checkAt (i, ty) = do
      checkType doc tyvars tmvars (take i (bsTmCtx bs)) ty
      Right ()

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
  checkTmVarModes doc (c2TmVars cell)
  ensureDistinctTyVars ("validateDoctrine: duplicate cell tyvars in " <> c2Name cell) (c2TyVars cell)
  ensureDistinctTmVars ("validateDoctrine: duplicate cell term vars in " <> c2Name cell) (c2TmVars cell)
  if dMode (c2LHS cell) /= dMode (c2RHS cell)
    then Left "validateDoctrine: cell has mode mismatch"
    else if dTmCtx (c2LHS cell) /= dTmCtx (c2RHS cell)
      then Left "validateDoctrine: cell has term-context mismatch"
    else do
      ctxL <- diagramDom (c2LHS cell)
      ctxR <- diagramDom (c2RHS cell)
      let tt = doctrineTypeTheory doc
      let tyFlexDom = S.unions (map freeTyVarsType (ctxL <> ctxR))
      let tmFlexDom = S.unions (map freeTmVarsType (ctxL <> ctxR))
      _ <- unifyCtx tt [] tyFlexDom tmFlexDom ctxL ctxR
      codL <- diagramCod (c2LHS cell)
      codR <- diagramCod (c2RHS cell)
      let tyFlexCod = S.unions (map freeTyVarsType (codL <> codR))
      let tmFlexCod = S.unions (map freeTmVarsType (codL <> codR))
      _ <- unifyCtx tt [] tyFlexCod tmFlexCod codL codR
      let lhsVars = freeTyVarsDiagram (c2LHS cell)
      let rhsVars = freeTyVarsDiagram (c2RHS cell)
      let declaredTy = S.fromList (c2TyVars cell)
      if S.isSubsetOf rhsVars (S.union lhsVars declaredTy)
        then Right ()
        else Left "validateDoctrine: RHS introduces fresh type variables"
      let lhsTmVars = freeTmVarsDiagram (c2LHS cell)
      let rhsTmVars = freeTmVarsDiagram (c2RHS cell)
      let declaredTm = S.fromList (c2TmVars cell)
      if S.isSubsetOf rhsTmVars (S.union lhsTmVars declaredTm)
        then Right ()
        else Left "validateDoctrine: RHS introduces fresh term variables"
      let lhsAttrVars = freeAttrVarsDiagram (c2LHS cell)
      let rhsAttrVars = freeAttrVarsDiagram (c2RHS cell)
      if S.isSubsetOf rhsAttrVars lhsAttrVars
        then Right ()
        else Left "Cell RHS introduces fresh attribute variables"
      let vars = S.union lhsVars rhsVars
      if S.isSubsetOf vars declaredTy
        then Right ()
        else Left "validateDoctrine: cell uses undeclared type variables"
      let tmVars = S.union lhsTmVars rhsTmVars
      if S.isSubsetOf tmVars declaredTm
        then Right ()
        else Left "validateDoctrine: cell uses undeclared term variables"
      let lhsCapturedMetas = binderArgMetaVarsDiagram (c2LHS cell)
      let rhsReferencedMetas = S.union (binderArgMetaVarsDiagram (c2RHS cell)) (spliceMetaVarsDiagram (c2RHS cell))
      if S.isSubsetOf rhsReferencedMetas lhsCapturedMetas
        then Right ()
        else Left "validateDoctrine: RHS references binder metas not captured by LHS binder arguments"

checkContext :: Doctrine -> ModeName -> [TyVar] -> [TmVar] -> [TypeExpr] -> Context -> Either Text ()
checkContext doc expectedMode tyvars tmvars tmCtx ctx = mapM_ (checkBoundaryType doc expectedMode tyvars tmvars tmCtx) ctx

checkBoundaryType :: Doctrine -> ModeName -> [TyVar] -> [TmVar] -> [TypeExpr] -> TypeExpr -> Either Text ()
checkBoundaryType doc expectedMode tyvars tmvars tmCtx ty = do
  checkType doc tyvars tmvars tmCtx ty
  if typeMode ty == expectedMode
    then Right ()
    else Left "validateDoctrine: generator boundary mode mismatch"

checkType :: Doctrine -> [TyVar] -> [TmVar] -> [TypeExpr] -> TypeExpr -> Either Text ()
checkType doc tyvars tmvars tmCtx ty =
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
      checkType doc tyvars tmvars tmCtx inner
      _ <- normalizeTypeExpr (dModes doc) ty
      Right ()
  where
    checkArg _ (PS_Ty m, TAType argTy) = do
      checkType doc tyvars tmvars tmCtx argTy
      if typeMode argTy == m
        then Right ()
        else Left "validateDoctrine: type constructor argument mode mismatch"
    checkArg _ (PS_Tm sortTy, TATm tmTerm) = do
      checkType doc tyvars tmvars tmCtx sortTy
      checkTmTerm doc tyvars tmvars tmCtx sortTy tmTerm
    checkArg _ _ = Left "validateDoctrine: type argument kind mismatch"

checkTmTerm :: Doctrine -> [TyVar] -> [TmVar] -> [TypeExpr] -> TypeExpr -> TermDiagram -> Either Text ()
checkTmTerm doc tyvars tmvars tmCtx expectedSort tm =
  do
    mapM_ checkMetaVar (S.toList (freeTmVarsTerm tm))
    _ <- termToDiagram tt tmCtx expectedSort tm
    pure ()
  where
    tt = doctrineTypeTheory doc

    checkMetaVar v = do
      if any (sameTmVarId v) tmvars
        then checkType doc tyvars tmvars tmCtx (tmvSort v)
        else Left "validateDoctrine: unknown term variable"

    sameTmVarId a b = tmvName a == tmvName b && tmvScope a == tmvScope b

ensureDistinctTyVars :: Text -> [TyVar] -> Either Text ()
ensureDistinctTyVars label vars =
  let names = map tvName vars
      set = S.fromList names
   in if S.size set == length names
        then Right ()
        else Left label

ensureDistinctTmVars :: Text -> [TmVar] -> Either Text ()
ensureDistinctTmVars label vars =
  let names = map tmvName vars
      set = S.fromList names
   in if S.size set == length names
        then Right ()
        else Left label

checkTyVarModes :: Doctrine -> [TyVar] -> Either Text ()
checkTyVarModes doc vars =
  if all (\v -> M.member (tvMode v) (mtModes (dModes doc))) vars
    then Right ()
    else Left "validateDoctrine: type variable has unknown mode"

checkTmVarModes :: Doctrine -> [TmVar] -> Either Text ()
checkTmVarModes doc vars =
  mapM_ checkOne vars
  where
    checkOne v = do
      checkType doc [] vars [] (tmvSort v)
      Right ()

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

checkAction :: Doctrine -> (ModName, ModAction) -> Either Text ()
checkAction doc (name, action) = do
  if maMod action == name
    then Right ()
    else Left "validateDoctrine: action declaration name mismatch"
  decl <-
    case M.lookup name (mtDecls (dModes doc)) of
      Nothing -> Left "validateDoctrine: action references unknown modality"
      Just d -> Right d
  let srcMode = mdSrc decl
  let tgtMode = mdTgt decl
  let srcGens = M.findWithDefault M.empty srcMode (dGens doc)
  let checkGenImage g = do
        img <-
          case M.lookup (srcMode, g) (maGenMap action) of
            Nothing -> Left "validateDoctrine: action is missing a generator image"
            Just d -> Right d
        if dMode img == tgtMode
          then Right ()
          else Left "validateDoctrine: action generator image has wrong mode"
        validateDiagram img
  mapM_ checkGenImage (M.keys srcGens)

checkObligation :: ObligationDecl -> Either Text ()
checkObligation obl = do
  validateDiagram (obLHS obl)
  validateDiagram (obRHS obl)
  if dMode (obLHS obl) == dMode (obRHS obl) && dTmCtx (obLHS obl) == dTmCtx (obRHS obl)
    then Right ()
    else Left "validateDoctrine: obligation boundary mismatch"

ensureDistinct :: Ord a => Text -> [a] -> Either Text ()
ensureDistinct label xs =
  if length (L.nub xs) == length xs
    then Right ()
    else Left label

renderGen :: GenName -> Text
renderGen (GenName t) = t
