{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Doctrine
  ( InputShape(..)
  , GenParam(..)
  , BinderSig(..)
  , GenDecl(..)
  , ModAction(..)
  , ObligationDecl(..)
  , Doctrine(..)
  , CtorTables
  , gdPlainDom
  , isTypeDeclGenNameInTables
  , mkTypeTheory
  , doctrineTypeTheory
  , doctrineTypeTheoryFromTables
  , deriveCtorTables
  , lookupCtorSigForOwnerInTables
  , lookupCtorRefForOwnerInTables
  , checkType
  , checkModTransformWitness
  , validateDoctrine
  , modeIsAcyclic
  ) where

import Data.Text (Text)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.IntMap.Strict as IM
import qualified Data.List as L
import qualified Data.Text as T
import Data.Maybe (mapMaybe)
import Control.Monad (foldM)
import Strat.Poly.ModeTheory
import Strat.Poly.Obj
import Strat.Poly.ObjClassifier (modeClassifierMode, modeUniverseObj)
import Strat.Poly.TypeTheory
  ( TypeTheory(..)
  , DefFragment(..)
  , TypeParamSig(..)
  , TmFunSig(..)
  , TmRule(..)
  , emptyDefFragment
  )
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Attr
import Strat.Poly.Diagram
import Strat.Poly.Graph (validateDiagram, Edge(..), EdgePayload(..), unPortId)
import Strat.Poly.Cell2
import Strat.Poly.DSL.AST (RawOblExpr(..))
import Strat.Poly.UnifyObj (unifyCtx)
import Strat.Common.Rules (RewritePolicy(..), RuleClass(..), Orientation(..))
import Strat.Poly.DefEq (termToDiagram, validateTermDiagram, defEqObj)
import Strat.Poly.Term.RewriteCompile (compileAllTermRules)
import Strat.Poly.Term.Termination (checkTerminatingSCT)
import Strat.Poly.Term.Confluence (checkConfluent)
import Strat.Poly.Term.AST (TermExpr(..))
import Strat.Poly.Term.RewriteSystem (TRS, mkTRS)
import qualified Strat.Poly.Term.RewriteSystem as RS

data BinderSig = BinderSig
  { bsTmCtx :: [Obj]
  , bsDom :: Context
  , bsCod :: Context
  } deriving (Eq, Ord, Show)

data InputShape
  = InPort Obj
  | InBinder BinderSig
  deriving (Eq, Ord, Show)

data GenParam
  = GP_Ty TmVar
  | GP_Tm TmVar
  deriving (Eq, Ord, Show)

data GenDecl = GenDecl
  { gdName :: GenName
  , gdMode :: ModeName
  , gdTyVars :: [TmVar]
  , gdTmVars :: [TmVar]
  , gdParams :: [GenParam]
  , gdDom :: [InputShape]
  , gdCod :: Context
  , gdAttrs :: [(AttrName, AttrSort)]
  } deriving (Eq, Show)

data ModAction = ModAction
  { maMod :: ModName
  , maGenMap :: M.Map (ModeName, GenName) Diagram
  , maPolicy :: RewritePolicy
  } deriving (Eq, Show)

data ObligationDecl = ObligationDecl
  { obName :: Text
  , obMode :: ModeName
  , obForGen :: Bool
  , obForGenName :: Maybe GenName
  , obGenerated :: Bool
  , obTyVars :: [TmVar]
  , obTmVars :: [TmVar]
  , obDom :: Context
  , obCod :: Context
  , obLHSExpr :: RawOblExpr
  , obRHSExpr :: RawOblExpr
  , obPolicy :: RewritePolicy
  } deriving (Eq, Show)

type CtorTables = M.Map ModeName (M.Map ObjName [TypeParamSig])

gdPlainDom :: GenDecl -> Context
gdPlainDom gd =
  [ ty
  | InPort ty <- gdDom gd
  ]

isTypeDeclGenNameInTables :: Doctrine -> CtorTables -> ModeName -> ObjName -> Bool
isTypeDeclGenNameInTables doc tables classifierMode ctorName =
  any
    (\(ownerMode, table) ->
        modeClassifierMode (dModes doc) ownerMode == classifierMode
          && M.member ctorName table
    )
    (M.toList tables)

data Doctrine = Doctrine
  { dName :: Text
  , dModes :: ModeTheory
  , dAcyclicModes :: S.Set ModeName
  , dAttrSorts :: M.Map AttrSort AttrSortDecl
  , dGens :: M.Map ModeName (M.Map GenName GenDecl)
  , dCells2 :: [Cell2]
  , dActions :: M.Map ModName ModAction
  , dObligations :: [ObligationDecl]
  } deriving (Eq, Show)

doctrineTypeTheory :: Doctrine -> Either Text TypeTheory
doctrineTypeTheory = mkTypeTheory

mkTypeTheory :: Doctrine -> Either Text TypeTheory
mkTypeTheory doc = do
  ctorTables <- deriveCtorTables doc
  mkTypeTheoryFromTables doc ctorTables

doctrineTypeTheoryFromTables :: Doctrine -> CtorTables -> Either Text TypeTheory
doctrineTypeTheoryFromTables = mkTypeTheoryFromTables

doctrineTypeTheoryBase :: Doctrine -> Either Text TypeTheory
doctrineTypeTheoryBase doc = do
  ctorTables <- deriveCtorTables doc
  doctrineTypeTheoryBaseFromTables doc ctorTables

mkTypeTheoryFromTables :: Doctrine -> CtorTables -> Either Text TypeTheory
mkTypeTheoryFromTables doc ctorTables = do
  tt0 <- doctrineTypeTheoryBaseFromTables doc ctorTables
  trs <- compileAllTermRules tt0
  let fragments = setFragmentTRS (dModes doc) (ttDefFragments tt0) trs
  mapM_ checkFragmentTermination (M.elems fragments)
  mapM_ checkFragmentConfluence (M.elems fragments)
  pure tt0 { ttDefFragments = fragments }

doctrineTypeTheoryBaseFromTables :: Doctrine -> CtorTables -> Either Text TypeTheory
doctrineTypeTheoryBaseFromTables doc ctorTables =
  let tmFuns = derivedTmFuns doc ctorTables
      tmRules = derivedTmRules doc tmFuns
      fragments0 = mkDefFragments (dModes doc) tmFuns tmRules M.empty
   in do
        ctorObjParams <- ctorObjParamsFromTables doc ctorTables
        pure
          TypeTheory
            { ttModes = dModes doc
            , ttCtorTables = ctorTables
            , ttObjParams = ctorObjParams
            , ttDefFragments = fragments0
            , ttStrictCtorLookup = True
            }
  where
    ctorObjParamsFromTables d tables =
      foldM insertOwner M.empty (M.toList tables)
      where
        insertOwner acc (ownerMode, table) =
          foldM (insertOne ownerMode) acc (M.toList table)
        insertOne ownerMode acc (ctorName, sig) =
          let classifierMode = modeClassifierMode (dModes d) ownerMode
              ref = ObjRef classifierMode ctorName
           in case M.lookup ref acc of
                Nothing -> Right (M.insert ref sig acc)
                Just sig0
                  | sig0 == sig -> Right acc
                  | otherwise ->
                      Left
                        ( "constructor `"
                            <> unObjName ctorName
                            <> "` has conflicting signatures across owner modes for classifier "
                            <> renderMode classifierMode
                        )

mkDefFragments
  :: ModeTheory
  -> M.Map ModeName (M.Map TmFunName TmFunSig)
  -> M.Map ModeName [TmRule]
  -> M.Map ModeName TRS
  -> M.Map ModeName DefFragment
mkDefFragments mt tmFuns tmRules tmTRS =
  M.fromList
    [ ( mode
      , DefFragment
          { dfMode = mode
          , dfFuns = M.findWithDefault M.empty mode tmFuns
          , dfRules = M.findWithDefault [] mode tmRules
          , dfTRS = M.findWithDefault (mkTRS mode []) mode tmTRS
          }
      )
    | mode <- M.keys (mtModes mt)
    ]

setFragmentTRS
  :: ModeTheory
  -> M.Map ModeName DefFragment
  -> M.Map ModeName TRS
  -> M.Map ModeName DefFragment
setFragmentTRS mt fragments tmTRS =
  M.fromList
    [ (mode, fragmentFor mode)
    | mode <- M.keys (mtModes mt)
    ]
  where
    fragmentFor mode =
      let base = M.findWithDefault (emptyDefFragment mode) mode fragments
       in base
            { dfTRS = M.findWithDefault (mkTRS mode []) mode tmTRS
            }

checkFragmentTermination :: DefFragment -> Either Text ()
checkFragmentTermination fragment =
  case checkTerminatingSCT (dfTRS fragment) of
    Right () -> Right ()
    Left err ->
      Left
        ( err
            <> "\n  root symbols: "
            <> renderRootSymbols (dfTRS fragment)
            <> "\n  fragment rules:\n"
            <> renderFragmentRules (dfTRS fragment)
        )

checkFragmentConfluence :: DefFragment -> Either Text ()
checkFragmentConfluence fragment =
  checkConfluent (dfTRS fragment)

renderRootSymbols :: TRS -> Text
renderRootSymbols trs =
  if null names
    then "(none)"
    else T.intercalate ", " names
  where
    names = S.toList (S.fromList (mapMaybe rootName (RS.trsRules trs)))
    rootName rule =
      case RS.trLHS rule of
        TMFun (TmFunName name) _ -> Just name
        _ -> Nothing

renderFragmentRules :: TRS -> Text
renderFragmentRules trs =
  if null linesOut
    then "    (none)"
    else T.unlines [ "    " <> line | line <- linesOut ]
  where
    linesOut =
      [ RS.trName rule <> ": " <> T.pack (show (RS.trLHS rule)) <> " -> " <> T.pack (show (RS.trRHS rule))
      | rule <- RS.trsRules trs
      ]

derivedTmFuns :: Doctrine -> CtorTables -> M.Map ModeName (M.Map TmFunName TmFunSig)
derivedTmFuns doc ctorTables =
  M.fromList
    [ (mode, funs)
    | (mode, table) <- M.toList (dGens doc)
    , let funs =
            M.fromList
              [ (TmFunName gName, TmFunSig { tfsArgs = [ ty | InPort ty <- gdDom gd ], tfsRes = res })
              | gd <- M.elems table
              , let GenName gName = gdName gd
              , not (isTypeDeclGenNameInTables doc ctorTables mode (ObjName gName))
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
cellPairToTmRule funs lhs0 rhs0 = do
  vars <- mkInputVars lhs0
  let varCtx = map tmvSort vars
  let lhs = lhs0 { dTmCtx = varCtx }
  let rhs = rhs0 { dTmCtx = varCtx }
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
      sortTy <- IM.lookup (unPortId pid) (dPortObj diag)
      pure TmVar { tmvName = "_x" <> T.pack (show i), tmvSort = sortTy, tmvScope = 0, tmvOwnerMode = Nothing }

validateDoctrine :: Doctrine -> Either Text ()
validateDoctrine doc = do
  checkModeTheory (dModes doc)
  if all (`M.member` mtModes (dModes doc)) (S.toList (dAcyclicModes doc))
    then Right ()
    else Left "validateDoctrine: acyclic mode references unknown mode"
  ctorTables <- deriveCtorTables doc
  tt <- mkTypeTheoryFromTables doc ctorTables
  checkComprehensionDecls doc ctorTables
  mapM_ checkAttrSortDecl (M.toList (dAttrSorts doc))
  mapM_ (checkGenTable doc tt) (M.toList (dGens doc))
  mapM_ (checkCell doc tt) (dCells2 doc)
  mapM_ (checkAction doc ctorTables) (M.toList (dActions doc))
  mapM_ (checkModeTransform doc) (M.elems (mtTransforms (dModes doc)))
  mapM_ (checkObligation doc tt) (dObligations doc)
  pure ()

checkComprehensionDecls :: Doctrine -> CtorTables -> Either Text ()
checkComprehensionDecls doc ctorTables =
  mapM_ checkOne (M.toList (mtClassifiedBy (dModes doc)))
  where
    checkOne (ownerMode, decl) =
      case cdComp decl of
        Nothing ->
          Left
            ( "validateDoctrine: mode "
                <> renderMode ownerMode
                <> " is classified and requires a comprehension declaration"
            )
        Just comp -> do
          checkField ownerMode "ctx_ext" (compCtxExt comp)
          checkField ownerMode "var" (compVar comp)
          checkField ownerMode "reindex" (compReindex comp)

    checkField ownerMode fieldName genName = do
      maybeGen <- lookupCompGen ownerMode fieldName genName
      case maybeGen of
        Nothing -> Right ()
        Just gen -> do
          checkNotCtor ownerMode fieldName genName
          checkShape ownerMode fieldName genName gen

    lookupCompGen ownerMode fieldName genName =
      case M.lookup ownerMode (dGens doc) >>= M.lookup genName of
        Just gd -> Right (Just gd)
        Nothing ->
          Left
            ( "validateDoctrine: comprehension "
                <> fieldName
                <> " generator "
                <> renderMode ownerMode
                <> "."
                <> renderGen genName
                <> " is not declared"
            )

    checkShape ownerMode fieldName genName gd = do
      if null (gdAttrs gd)
        then Right ()
        else
          Left
            ( "validateDoctrine: comprehension "
                <> fieldName
                <> " generator "
                <> renderMode ownerMode
                <> "."
                <> renderGen genName
                <> " must not have attributes"
            )
      case gdDom gd of
        [InPort _] -> Right ()
        _ ->
          Left
            ( "validateDoctrine: comprehension "
                <> fieldName
                <> " generator "
                <> renderMode ownerMode
                <> "."
                <> renderGen genName
                <> " must have exactly one input port and no binder inputs"
            )
      case gdCod gd of
        [_] -> Right ()
        _ ->
          Left
            ( "validateDoctrine: comprehension "
                <> fieldName
                <> " generator "
                <> renderMode ownerMode
                <> "."
                <> renderGen genName
                <> " must have exactly one output"
            )

    checkNotCtor ownerMode fieldName genName =
      if isTypeDeclGenNameInTables doc ctorTables ownerMode (ObjName (renderGen genName))
        then
          Left
            ( "validateDoctrine: comprehension "
                <> fieldName
                <> " generator "
                <> renderMode ownerMode
                <> "."
                <> renderGen genName
                <> " resolves as a constructor-like declaration"
            )
        else Right ()

    renderMode (ModeName n) = n
    renderGen (GenName n) = n

modeIsAcyclic :: Doctrine -> ModeName -> Bool
modeIsAcyclic doc mode = mode `S.member` dAcyclicModes doc

deriveCtorTables :: Doctrine -> Either Text (M.Map ModeName (M.Map ObjName [TypeParamSig]))
deriveCtorTables doc = do
  let ownerModes = M.keys (mtModes (dModes doc))
  seedPairs <- mapM seedForOwner ownerModes
  let seed = M.fromList seedPairs
  iterateFixedPoint (maxIterations ownerModes) seed
  where
    maxIterations ownerModes =
      1
        + sum
          [ length (candidateCtors ownerMode)
          | ownerMode <- ownerModes
          ]

    iterateFixedPoint remaining tables
      | remaining <= (0 :: Int) =
          Left "deriveCtorTables: fixed-point eligibility did not converge"
      | otherwise = do
          tt <- buildTypeTheory tables
          tables' <- foldM (growOwner tt) tables (M.keys (mtModes (dModes doc)))
          if tables' == tables
            then Right tables
            else iterateFixedPoint (remaining - 1) tables'

    buildTypeTheory tables = do
      tt0 <- doctrineTypeTheoryBaseFromTables doc tables
      trs <- compileAllTermRules tt0
      pure tt0 { ttDefFragments = setFragmentTRS (dModes doc) (ttDefFragments tt0) trs }

    seedForOwner ownerMode = do
      let classifierMode = modeClassifierMode (dModes doc) ownerMode
      implicit <- implicitForOwner classifierMode ownerMode
      pure (ownerMode, implicit)

    growOwner tt acc ownerMode = do
      let existing = M.findWithDefault M.empty ownerMode acc
      discovered <- eligibleForOwner tt ownerMode
      merged <- mergeCtorTables existing discovered
      pure (M.insert ownerMode merged acc)

    implicitForOwner classifierMode ownerMode =
      case modeUniverseObj (dModes doc) ownerMode of
        Just universe
          | not (isPendingUniverse universe) -> do
              universeNorm <- normalizeObjExpr (dModes doc) universe
              implicitUniverseCtor classifierMode universeNorm
        _ -> Right M.empty

    eligibleForOwner tt ownerMode = do
      let classifierMode = modeClassifierMode (dModes doc) ownerMode
      case modeUniverseObj (dModes doc) ownerMode of
        Just universe
          | not (isPendingUniverse universe) -> do
              universeNorm <- normalizeObjExpr (dModes doc) universe
              fromGens <- foldM (addCtor tt universeNorm) M.empty (candidateCtors ownerMode)
              implicit <- implicitUniverseCtor classifierMode universeNorm
              mergeCtorTables fromGens implicit
        _ -> Right M.empty

    candidateCtors ownerMode =
      let classifierMode = modeClassifierMode (dModes doc) ownerMode
       in [ gd
          | gd <- M.elems (M.findWithDefault M.empty classifierMode (dGens doc))
          , isCtorLike gd
          ]

    implicitUniverseCtor classifierMode universeNorm =
      case universeNorm of
        Obj _ (CTCon ref [])
          | orMode ref == classifierMode ->
              Right (M.singleton (orName ref) [])
        _ -> Right M.empty

    addCtor tt universeNorm acc gd =
      case gdCod gd of
        [codTy] -> do
          include <- eligibilityDefEq tt (map tmvSort (gdTmVars gd)) codTy universeNorm
          if include
            then do
              sig <- ctorSigFromGen gd
              insertCtorSig (genToObjName (gdName gd)) sig acc
            else Right acc
        _ -> Right acc

    eligibilityDefEq tt tmCtx codTy universeNorm =
      case defEqObj tt tmCtx codTy universeNorm of
        Right ok -> Right ok
        Left _ -> Right False

    isCtorLike gd =
      null (gdAttrs gd) && null (gdDom gd)

    mergeCtorTables a b =
      foldM
        (\acc (name, sig) -> insertCtorSig name sig acc)
        a
        (M.toList b)

    ctorSigFromGen gd = do
      let tyVars = gdTyVars gd
      let tmVars = gdTmVars gd
      let tySet = S.fromList tyVars
      mapM_ (ensureClosedTmSort tySet) tmVars
      pure
        [ case gp of
            GP_Ty v -> TPS_Ty (tyVarOwnerMode v)
            GP_Tm v -> TPS_Tm (tmvSort v)
        | gp <- gdParams gd
        ]
      where
        ensureClosedTmSort tySet tmVar =
          let bad = S.intersection (freeObjVarsObj (tmvSort tmVar)) tySet
           in if S.null bad
                then Right ()
                else
                  Left
                    ( "constructor generator `"
                        <> renderGen (gdName gd)
                        <> "` has term parameter `"
                        <> tmvName tmVar
                        <> "` whose sort mentions type parameters; this is not supported in this Phase 6 cut"
                    )

    insertCtorSig name sig acc =
      case M.lookup name acc of
        Nothing -> Right (M.insert name sig acc)
        Just sig0
          | sig0 == sig -> Right acc
          | otherwise ->
              Left
                ( "duplicate constructor `"
                    <> unObjName name
                    <> "` with incompatible signatures in classifier vocabulary"
                )

    genToObjName (GenName name) = ObjName name
    isPendingUniverse obj =
      case objCode obj of
        CTMeta v -> tmvName v == "__pending_universe"
        _ -> False

genParamsMatchDecls :: GenDecl -> Bool
genParamsMatchDecls gd =
  mapMaybe pickTy (gdParams gd) == gdTyVars gd
    && mapMaybe pickTm (gdParams gd) == gdTmVars gd
    && length (gdParams gd) == length (gdTyVars gd) + length (gdTmVars gd)
  where
    pickTy gp =
      case gp of
        GP_Ty v -> Just v
        GP_Tm _ -> Nothing
    pickTm gp =
      case gp of
        GP_Ty _ -> Nothing
        GP_Tm v -> Just v

lookupCtorRefForOwnerInTables :: Doctrine -> CtorTables -> ModeName -> ObjName -> Maybe ObjRef
lookupCtorRefForOwnerInTables doc tables ownerMode ctorName =
  case M.lookup ctorName table of
    Nothing -> Nothing
    Just _ -> Just (ObjRef classifierMode ctorName)
  where
    classifierMode = modeClassifierMode (dModes doc) ownerMode
    table = M.findWithDefault M.empty ownerMode tables

lookupCtorSigForOwnerInTables :: Doctrine -> CtorTables -> ModeName -> ObjRef -> Either Text [TypeParamSig]
lookupCtorSigForOwnerInTables doc tables ownerMode ref = do
  let classifierMode = modeClassifierMode (dModes doc) ownerMode
  if orMode ref == classifierMode
    then Right ()
    else
      Left
        ( "constructor qualifier mode mismatch: owner mode "
            <> renderMode ownerMode
            <> " is classified by "
            <> renderMode classifierMode
        )
  let table = M.findWithDefault M.empty ownerMode tables
  case M.lookup (orName ref) table of
    Nothing ->
      Left
        ( "unknown constructor `"
            <> unObjName (orName ref)
            <> "` for owner mode "
            <> renderMode ownerMode
            <> " (classifier "
            <> renderMode classifierMode
            <> "); available: "
            <> renderCtorNames (M.keys table)
        )
    Just sig -> Right sig
  where
    renderCtorNames [] = "(none)"
    renderCtorNames names = T.intercalate ", " (map unObjName names)

checkModeTheory :: ModeTheory -> Either Text ()
checkModeTheory = checkWellFormed

checkGenTable :: Doctrine -> TypeTheory -> (ModeName, M.Map GenName GenDecl) -> Either Text ()
checkGenTable doc tt (mode, gens)
  | M.member mode (mtModes (dModes doc)) = mapM_ (checkGen doc tt mode) (M.elems gens)
  | otherwise = Left "validateDoctrine: generators for unknown mode"

checkGen :: Doctrine -> TypeTheory -> ModeName -> GenDecl -> Either Text ()
checkGen doc tt mode gd
  | gdMode gd /= mode = Left "validateDoctrine: generator stored under wrong mode"
  | otherwise = do
      if genParamsMatchDecls gd
        then Right ()
        else Left "validateDoctrine: generator parameter order metadata mismatch"
      checkTyVarModes doc (gdTyVars gd)
      checkTmVarModes doc tt (gdTyVars gd) (gdTmVars gd)
      ensureDistinctTyVars ("validateDoctrine: duplicate generator tyvars in " <> renderGen (gdName gd)) (gdTyVars gd)
      ensureDistinctTmVars ("validateDoctrine: duplicate generator term vars in " <> renderGen (gdName gd)) (gdTmVars gd)
      mapM_ (checkInputShape doc tt mode (gdTyVars gd) (gdTmVars gd)) (gdDom gd)
      checkContext doc tt mode (gdTyVars gd) (gdTmVars gd) [] (gdCod gd)
      checkGenAttrs doc gd

checkInputShape :: Doctrine -> TypeTheory -> ModeName -> [TmVar] -> [TmVar] -> InputShape -> Either Text ()
checkInputShape doc tt expectedMode tyvars tmvars shape =
  case shape of
    InPort ty -> checkBoundaryType doc tt expectedMode tyvars tmvars [] ty
    InBinder bs -> checkBinderSig doc tt expectedMode tyvars tmvars bs

checkBinderSig :: Doctrine -> TypeTheory -> ModeName -> [TmVar] -> [TmVar] -> BinderSig -> Either Text ()
checkBinderSig doc tt expectedMode tyvars tmvars bs = do
  checkTmCtxTele (bsTmCtx bs)
  checkContext doc tt expectedMode tyvars tmvars (bsTmCtx bs) (bsDom bs)
  checkContext doc tt expectedMode tyvars tmvars (bsTmCtx bs) (bsCod bs)
  where
    checkTmCtxTele ctx =
      mapM_ checkAt (zip [0 :: Int ..] ctx)

    checkAt (i, ty) = do
      checkType doc tt tyvars tmvars (take i (bsTmCtx bs)) ty
      Right ()

checkCell :: Doctrine -> TypeTheory -> Cell2 -> Either Text ()
checkCell doc tt cell = do
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
  checkTmVarModes doc tt (c2TyVars cell) (c2TmVars cell)
  ensureDistinctTyVars ("validateDoctrine: duplicate cell tyvars in " <> c2Name cell) (c2TyVars cell)
  ensureDistinctTmVars ("validateDoctrine: duplicate cell term vars in " <> c2Name cell) (c2TmVars cell)
  if dMode (c2LHS cell) /= dMode (c2RHS cell)
    then Left "validateDoctrine: cell has mode mismatch"
    else if dTmCtx (c2LHS cell) /= dTmCtx (c2RHS cell)
      then Left "validateDoctrine: cell has term-context mismatch"
    else do
      let tmCtx = dTmCtx (c2LHS cell)
      ctxL <- diagramDom (c2LHS cell)
      ctxR <- diagramDom (c2RHS cell)
      let tyFlexDom = S.unions (map freeObjVarsObj (ctxL <> ctxR))
      let tmFlexDom = S.unions (map freeTmVarsObj (ctxL <> ctxR))
      let flexDom = S.union tyFlexDom tmFlexDom
      _ <- unifyCtx tt tmCtx flexDom ctxL ctxR
      codL <- diagramCod (c2LHS cell)
      codR <- diagramCod (c2RHS cell)
      let tyFlexCod = S.unions (map freeObjVarsObj (codL <> codR))
      let tmFlexCod = S.unions (map freeTmVarsObj (codL <> codR))
      let flexCod = S.union tyFlexCod tmFlexCod
      _ <- unifyCtx tt tmCtx flexCod codL codR
      let lhsVars = freeObjVarsDiagram (c2LHS cell)
      let rhsVars = freeObjVarsDiagram (c2RHS cell)
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

checkContext :: Doctrine -> TypeTheory -> ModeName -> [TmVar] -> [TmVar] -> [Obj] -> Context -> Either Text ()
checkContext doc tt expectedMode tyvars tmvars tmCtx ctx = mapM_ (checkBoundaryType doc tt expectedMode tyvars tmvars tmCtx) ctx

checkBoundaryType :: Doctrine -> TypeTheory -> ModeName -> [TmVar] -> [TmVar] -> [Obj] -> Obj -> Either Text ()
checkBoundaryType doc tt expectedMode tyvars tmvars tmCtx ty = do
  checkType doc tt tyvars tmvars tmCtx ty
  if objOwnerMode ty == expectedMode
    then Right ()
    else Left "validateDoctrine: generator boundary mode mismatch"

checkType :: Doctrine -> TypeTheory -> [TmVar] -> [TmVar] -> [Obj] -> Obj -> Either Text ()
checkType doc tt tyvars tmvars tmCtx ty =
  case ty of
    OVar v ->
      if v `elem` tyvars
        then
          if M.member (tyVarOwnerMode v) (mtModes (dModes doc))
            then Right ()
            else Left "validateDoctrine: type variable has unknown mode"
        else Left "validateDoctrine: unknown type variable"
    OCon ref args -> do
      params <- lookupCtorSigForOwnerInTables doc (ttCtorTables tt) (objOwnerMode ty) ref
      if length params /= length args
        then Left "validateDoctrine: type constructor arity mismatch"
        else mapM_ (checkArg ref) (zip params args)
    OMod _ inner -> do
      checkType doc tt tyvars tmvars tmCtx inner
      _ <- normalizeObjExpr (dModes doc) ty
      Right ()
  where
    checkArg _ (TPS_Ty m, OAObj argTy) = do
      checkType doc tt tyvars tmvars tmCtx argTy
      if objOwnerMode argTy == m
        then Right ()
        else Left "validateDoctrine: type constructor argument mode mismatch"
    checkArg _ (TPS_Tm sortTy, OATm tmTerm) = do
      checkType doc tt tyvars tmvars tmCtx sortTy
      checkTmTerm doc tt tyvars tmvars tmCtx sortTy tmTerm
    checkArg _ _ = Left "validateDoctrine: type argument kind mismatch"

checkTmTerm :: Doctrine -> TypeTheory -> [TmVar] -> [TmVar] -> [Obj] -> Obj -> TermDiagram -> Either Text ()
checkTmTerm doc tt tyvars tmvars tmCtx expectedSort tm =
  do
    mapM_ checkMetaVar (S.toList (freeTmVarsTerm tm))
    _ <- termToDiagram tt tmCtx expectedSort tm
    pure ()
  where
    checkMetaVar v = do
      if any (sameTmVarId v) tmvars
        then checkType doc tt tyvars tmvars tmCtx (tmvSort v)
        else Left "validateDoctrine: unknown term variable"

    sameTmVarId a b = tmvName a == tmvName b && tmvScope a == tmvScope b

ensureDistinctTyVars :: Text -> [TmVar] -> Either Text ()
ensureDistinctTyVars label vars =
  let names = map tmvName vars
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

checkTyVarModes :: Doctrine -> [TmVar] -> Either Text ()
checkTyVarModes doc vars =
  if all (\v -> M.member (tyVarOwnerMode v) (mtModes (dModes doc))) vars
    then Right ()
    else Left "validateDoctrine: type variable has unknown mode"

checkTmVarModes :: Doctrine -> TypeTheory -> [TmVar] -> [TmVar] -> Either Text ()
checkTmVarModes doc tt tyVars vars =
  mapM_ checkOne vars
  where
    checkOne v = do
      checkType doc tt tyVars vars [] (tmvSort v)
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

checkAction :: Doctrine -> CtorTables -> (ModName, ModAction) -> Either Text ()
checkAction doc ctorTables (name, action) = do
  if maMod action == name
    then Right ()
    else Left "validateDoctrine: action declaration name mismatch"
  decl <-
    case M.lookup name (mtDecls (dModes doc)) of
      Nothing -> Left "validateDoctrine: action references unknown modality"
      Just d -> Right d
  let srcMode = mdSrc decl
  let tgtMode = mdTgt decl
  let compSupportNames =
        case M.lookup srcMode (mtClassifiedBy (dModes doc)) >>= cdComp of
          Just comp ->
            S.fromList [compCtxExt comp, compVar comp, compReindex comp]
          Nothing -> S.empty
  let srcGens =
        M.filterWithKey
          ( \gName _ ->
              gName `S.notMember` compSupportNames
                && not
                  ( isTypeDeclGenNameInTables
                      doc
                      ctorTables
                      srcMode
                      (ObjName (renderGen gName))
                  )
          )
          (M.findWithDefault M.empty srcMode (dGens doc))
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

checkModeTransform :: Doctrine -> ModTransformDecl -> Either Text ()
checkModeTransform doc decl = do
  let witnessMode = meTgt (mtdFrom decl)
  witnessGen <-
    case M.lookup witnessMode (dGens doc) >>= M.lookup (mtdWitness decl) of
      Nothing -> Left "validateDoctrine: modality transform witness references unknown generator"
      Just gen -> Right gen
  checkModTransformWitness doc (mtdFrom decl) (mtdTo decl) witnessGen

checkObligation :: Doctrine -> TypeTheory -> ObligationDecl -> Either Text ()
checkObligation doc tt obl = do
  ensureDistinctTyVars ("validateDoctrine: duplicate obligation tyvars in " <> obName obl) (obTyVars obl)
  ensureDistinctTmVars ("validateDoctrine: duplicate obligation term vars in " <> obName obl) (obTmVars obl)
  if obForGen obl
    then do
      case obForGenName obl of
        Nothing -> Right ()
        Just targetGen ->
          case M.lookup (obMode obl) (dGens doc) >>= M.lookup targetGen of
            Nothing ->
              Left
                ( "validateDoctrine: obligation "
                    <> obName obl
                    <> " references unknown generator "
                    <> renderMode (obMode obl)
                    <> "."
                    <> renderGen targetGen
                )
            Just _ -> Right ()
      if null (obTyVars obl) && null (obTmVars obl) && null (obDom obl) && null (obCod obl)
        then Right ()
        else Left "validateDoctrine: for_gen obligation must not declare vars or boundary signature"
      ensureNoGenRefs False (obLHSExpr obl)
      ensureNoGenRefs False (obRHSExpr obl)
    else do
      case obForGenName obl of
        Nothing -> Right ()
        Just _ ->
          Left "validateDoctrine: obligation target generator requires for_gen"
      checkContext doc tt (obMode obl) (obTyVars obl) (obTmVars obl) [] (obDom obl)
      checkContext doc tt (obMode obl) (obTyVars obl) (obTmVars obl) [] (obCod obl)
      ensureNoGenRefs True (obLHSExpr obl)
      ensureNoGenRefs True (obRHSExpr obl)
  where
    ensureNoGenRefs allow expr =
      case expr of
        ROEDiag _ -> Right ()
        ROEMap _ inner -> ensureNoGenRefs allow inner
        ROEGen ->
          if allow
            then Left "validateDoctrine: @gen is only allowed in for_gen obligations"
            else Right ()
        ROELiftDom _
          | allow -> Left "validateDoctrine: lift_dom is only allowed in for_gen obligations"
          | otherwise -> Right ()
        ROELiftCod _
          | allow -> Left "validateDoctrine: lift_cod is only allowed in for_gen obligations"
          | otherwise -> Right ()
        ROEComp a b -> ensureNoGenRefs allow a >> ensureNoGenRefs allow b
        ROETensor a b -> ensureNoGenRefs allow a >> ensureNoGenRefs allow b

checkModTransformWitness :: Doctrine -> ModExpr -> ModExpr -> GenDecl -> Either Text ()
checkModTransformWitness doc fromMe toMe witness = do
  let witnessMode = meTgt fromMe
  if gdMode witness == witnessMode
    then Right ()
    else Left "mod_transform: witness generator is declared in the wrong mode"
  tyVar <-
    case gdTyVars witness of
      [v] -> Right v
      _ -> Left "mod_transform: witness generator must have exactly one type variable"
  if tyVarOwnerMode tyVar == meSrc fromMe
    then Right ()
    else Left "mod_transform: witness type variable must live in transform source mode"
  if null (gdTmVars witness)
    then Right ()
    else Left "mod_transform: witness generator must not have term variables"
  if null (gdAttrs witness)
    then Right ()
    else Left "mod_transform: witness generator must not have attributes"
  domTy <-
    case gdDom witness of
      [InPort ty] -> Right ty
      _ -> Left "mod_transform: witness generator domain must be exactly one input port"
  codTy <-
    case gdCod witness of
      [ty] -> Right ty
      _ -> Left "mod_transform: witness generator codomain must be exactly one output port"
  let expectedDom = OMod fromMe (OVar tyVar)
  let expectedCod = OMod toMe (OVar tyVar)
  domNorm <- normalizeObjExpr (dModes doc) domTy
  codNorm <- normalizeObjExpr (dModes doc) codTy
  expectedDomNorm <- normalizeObjExpr (dModes doc) expectedDom
  expectedCodNorm <- normalizeObjExpr (dModes doc) expectedCod
  if domNorm == expectedDomNorm && codNorm == expectedCodNorm
    then Right ()
    else Left "mod_transform: witness generator must have type [mu(A)] -> [nu(A)] for the declared transform"

ensureDistinct :: Ord a => Text -> [a] -> Either Text ()
ensureDistinct label xs =
  if length (L.nub xs) == length xs
    then Right ()
    else Left label

tyVarOwnerMode :: TmVar -> ModeName
tyVarOwnerMode v =
  case tmvOwnerMode v of
    Just owner -> owner
    Nothing -> objOwnerMode (tmvSort v)

renderGen :: GenName -> Text
renderGen (GenName t) = t

unObjName :: ObjName -> Text
unObjName (ObjName t) = t

renderMode :: ModeName -> Text
renderMode (ModeName t) = t
