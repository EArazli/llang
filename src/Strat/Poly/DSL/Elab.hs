{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.DSL.Elab
  ( elabPolyDoctrine
  , elabPolyDoctrineWithBudget
  , elabPolyDoctrineWithBudgetResult
  , elabPolyDoctrineFromBaseWithBudgetResult
  , elabPolyMorphism
  , elabPolyMorphismWithBudget
  , elabPolyMorphismWithBudgetResult
  , elabDiagExpr
  , ImplementsCheckResult(..)
  , ImplementsProof(..)
  , checkImplementsObligationsWithBudget
  , checkImplementsObligations
  , identityMorphismFor
  , parsePolicy
  ) where

import Control.Monad (foldM, when)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import Strat.Common.Rules (RewritePolicy(..))
import Strat.DSL.AST
  ( RawPolyAttrSortMap(..)
  , RawPolyGenMap(..)
  , RawPolyModeMap(..)
  , RawPolyModalityMap(..)
  , RawPolyMorphism(..)
  , RawPolyMorphismItem(..)
  , RawPolyTypeMap(..)
  )
import Strat.Frontend.Env (ModuleEnv(..))
import Strat.Poly.Attr (AttrSort(..))
import Strat.Poly.DSL.Elab.Diag
  ( BinderMetaMode(..)
  , elabDiagExpr
  , elabDiagExprWith
  , ensureAttrSort
  , ensureMode
  , lookupGen
  , renderGenName
  , renderModeName
  , unifyBoundary
  )
import Strat.Poly.DSL.Elab.DoctrinePhase
  ( elabPolyDoctrine
  , elabPolyDoctrineFromBaseWithBudgetResult
  , elabPolyDoctrineWithBudget
  , elabPolyDoctrineWithBudgetResult
  , identityMorphismFor
  )
import Strat.Poly.DSL.Elab.Implements
  ( ImplementsCheckResult(..)
  , ImplementsProof(..)
  , checkImplementsObligations
  , checkImplementsObligationsWithBudget
  )
import Strat.Poly.DSL.Elab.Resolve (elabRawModExpr)
import Strat.Poly.DSL.Elab.Term
  ( buildTypeTemplateParams
  , elabObjExpr
  , ownerModeForTypeMeta
  )
import Strat.Poly.Diagram
import Strat.Poly.Doctrine
import Strat.Poly.Graph (BinderMetaVar(..))
import Strat.Poly.ModeTheory
import Strat.Poly.Morphism
import Strat.Poly.Names
import Strat.Poly.Obj
import Strat.Poly.Proof
  ( SearchBudget(..)
  , defaultSearchBudget
  , renderSearchLimit
  )

elabPolyMorphism :: ModuleEnv -> RawPolyMorphism -> Either Text Morphism
elabPolyMorphism env raw = fst <$> elabPolyMorphismWithBudgetResult defaultSearchBudget env raw

elabPolyMorphismWithBudget :: SearchBudget -> ModuleEnv -> RawPolyMorphism -> Either Text Morphism
elabPolyMorphismWithBudget budget env raw =
  fst <$> elabPolyMorphismWithBudgetResult budget env raw

elabPolyMorphismWithBudgetResult :: SearchBudget -> ModuleEnv -> RawPolyMorphism -> Either Text (Morphism, MorphismCheckResult)
elabPolyMorphismWithBudgetResult budgetDefault env raw = do
  src <- lookupPolyDoctrine env (rpmSrc raw)
  tgt <- lookupPolyDoctrine env (rpmTgt raw)
  srcCtorTables <- deriveCtorTables src
  ttSrc <- doctrineTypeTheoryFromTables src srcCtorTables
  tgtCtorTables <- deriveCtorTables tgt
  ttTgt <- doctrineTypeTheoryFromTables tgt tgtCtorTables
  let checkName = maybe "all" id (rpmCheck raw)
  checkMode <- parseMorphismCheck checkName
  let policyName = maybe "UseStructuralAsBidirectional" id (rpmPolicy raw)
  policy <- parsePolicy policyName
  let budget = morphismBudget budgetDefault raw
  let coercionFlags = [() | RPMCoercion <- rpmItems raw]
  when (length coercionFlags > 1) (Left "morphism: duplicate coercion flag")
  modeMap <- buildModeMap src tgt [ m | RPMMode m <- rpmItems raw ]
  modMap <- buildModMap src tgt modeMap [ mm | RPMModality mm <- rpmItems raw ]
  attrSortMap <- buildAttrSortMap src tgt [ a | RPMAttrSort a <- rpmItems raw ]
  typeMap <- foldM (addTypeMap src srcCtorTables tgt modeMap) M.empty [ t | RPMType t <- rpmItems raw ]
  let mor0 = Morphism
        { morName = rpmName raw
        , morSrc = src
        , morTgt = tgt
        , morIsCoercion = not (null coercionFlags)
        , morModeMap = modeMap
        , morModMap = modMap
        , morAttrSortMap = attrSortMap
        , morTypeMap = typeMap
        , morGenMap = M.empty
        , morCheck = checkMode
        , morPolicy = policy
        }
  genMap <- foldM (addGenMap src tgt ttSrc ttTgt tgtCtorTables modeMap mor0) M.empty [ g | RPMGen g <- rpmItems raw ]
  ensureAllGenMapped src srcCtorTables genMap
  let mor = Morphism
        { morName = rpmName raw
        , morSrc = src
        , morTgt = tgt
        , morIsCoercion = not (null coercionFlags)
        , morModeMap = modeMap
        , morModMap = modMap
        , morAttrSortMap = attrSortMap
        , morTypeMap = typeMap
        , morGenMap = genMap
        , morCheck = checkMode
        , morPolicy = policy
        }
  case checkMorphismResultWithBudget budget mor of
    Left err ->
      Left ("morphism " <> rpmName raw <> ": " <> err)
    Right result ->
      case result of
        MorphismCheckProved _ ->
          Right (mor, result)
        MorphismCheckUndecided cellName lim ->
          Left
            ( "morphism "
                <> rpmName raw
                <> ": checkMorphism: equation undecided for "
                <> cellName
                <> " ("
                <> renderSearchLimit lim
                <> ")"
            )
  where
    lookupPolyDoctrine env' name =
      case M.lookup name (meDoctrines env') of
        Nothing -> Left ("Unknown doctrine: " <> name)
        Just doc -> Right doc
    buildModeMap src tgt decls = do
      let srcModes = mtModes (dModes src)
      let tgtModes = mtModes (dModes tgt)
      pairs <- mapM toPair decls
      let dup = firstDup (map fst pairs)
      case dup of
        Just m -> Left ("morphism: duplicate mode mapping for " <> renderModeNameLocal m)
        Nothing -> Right ()
      let explicit = M.fromList pairs
      let missing = [ m | m <- M.keys srcModes, M.notMember m explicit, M.notMember m tgtModes ]
      case missing of
        (m:_) -> Left ("morphism: missing mode mapping for " <> renderModeNameLocal m)
        [] -> Right ()
      let full =
            M.fromList
              [ (m, M.findWithDefault m m explicit)
              | m <- M.keys srcModes
              ]
      pure full
      where
        toPair (RawPolyModeMap srcText tgtText) = do
          let srcMode = ModeName srcText
          let tgtMode = ModeName tgtText
          ensureMode src srcMode
          ensureMode tgt tgtMode
          pure (srcMode, tgtMode)
        renderModeNameLocal (ModeName name) = name
        firstDup xs = go S.empty xs
          where
            go _ [] = Nothing
            go seen (x:rest)
              | x `S.member` seen = Just x
              | otherwise = go (S.insert x seen) rest
    buildAttrSortMap src tgt decls = do
      pairs <- mapM toPair decls
      let dup = firstDup (map fst pairs)
      case dup of
        Just s -> Left ("morphism: duplicate attrsort mapping for " <> renderAttrSort s)
        Nothing -> Right ()
      pure (M.fromList pairs)
      where
        toPair decl = do
          let srcSort = AttrSort (rpmasSrc decl)
          let tgtSort = AttrSort (rpmasTgt decl)
          ensureAttrSort src srcSort
          ensureAttrSort tgt tgtSort
          pure (srcSort, tgtSort)
        renderAttrSort (AttrSort name) = name
        firstDup xs = go S.empty xs
          where
            go _ [] = Nothing
            go seen (x:rest)
              | x `S.member` seen = Just x
              | otherwise = go (S.insert x seen) rest
    buildModMap src tgt modeMap decls = do
      explicitPairs <- mapM toExplicit decls
      let dup = firstDup (map fst explicitPairs)
      case dup of
        Just m -> Left ("morphism: duplicate modality mapping for " <> renderModName m)
        Nothing -> Right ()
      let explicit = M.fromList explicitPairs
      fillDefaults explicit (M.toList (mtDecls (dModes src)))
      where
        firstDup xs = go S.empty xs
          where
            go _ [] = Nothing
            go seen (x:rest)
              | x `S.member` seen = Just x
              | otherwise = go (S.insert x seen) rest
        toExplicit (RawPolyModalityMap srcText tgtRaw) = do
          let srcName = ModName srcText
          srcDecl <- requireDecl (dModes src) srcName
          tgtExpr0 <- elabRawModExpr (dModes tgt) tgtRaw
          let tgtExpr = normalizeModExpr (dModes tgt) tgtExpr0
          srcMode <- lookupModeMap modeMap (mdSrc srcDecl)
          tgtMode <- lookupModeMap modeMap (mdTgt srcDecl)
          if meSrc tgtExpr /= srcMode || meTgt tgtExpr /= tgtMode
            then Left ("morphism: modality map mode mismatch for " <> renderModName srcName)
            else Right (srcName, tgtExpr)
        fillDefaults acc [] = Right acc
        fillDefaults acc ((srcName, srcDecl):rest) =
          case M.lookup srcName acc of
            Just _ -> fillDefaults acc rest
            Nothing -> do
              srcMode <- lookupModeMap modeMap (mdSrc srcDecl)
              tgtMode <- lookupModeMap modeMap (mdTgt srcDecl)
              defaultExpr <- defaultMap srcName srcMode tgtMode
              fillDefaults (M.insert srcName defaultExpr acc) rest
        defaultMap srcName srcMode tgtMode =
          case M.lookup srcName (mtDecls (dModes tgt)) of
            Just decl
              | mdSrc decl == srcMode && mdTgt decl == tgtMode ->
                  Right ModExpr { meSrc = srcMode, meTgt = tgtMode, mePath = [srcName] }
            _ -> Left ("morphism: unmapped modality " <> renderModName srcName)
        requireDecl mt name =
          case M.lookup name (mtDecls mt) of
            Nothing -> Left ("morphism: unknown source modality " <> renderModName name)
            Just decl -> Right decl
        renderModName (ModName n) = n
    lookupModeMap modeMap mode =
      case M.lookup mode modeMap of
        Nothing -> Left "morphism: missing mode mapping"
        Just mode' -> Right mode'
    mapTyVarMode ttSrc ttTgt tgtTables mor v = do
      ownerSrc <- ownerModeForTypeMeta (morSrc mor) v
      ownerTgt <- applyMorphismMode mor ownerSrc
      sort' <- applyMorphismTyWithCaches ttSrc ttTgt tgtTables mor (tmvSort v)
      pure v { tmvSort = sort', tmvOwnerMode = Just ownerTgt }
    mapTmVarSort ttSrc ttTgt tgtTables mor v = do
      sort' <- applyMorphismTyWithCaches ttSrc ttTgt tgtTables mor (tmvSort v)
      pure v { tmvSort = sort', tmvOwnerMode = Nothing }
    addTypeMap src srcTables tgt modeMap mp decl = do
      let modeSrc = ModeName (rpmtSrcMode decl)
      let modeTgtDecl = ModeName (rpmtTgtMode decl)
      ensureMode src modeSrc
      ensureMode tgt modeTgtDecl
      modeTgtExpected <- lookupModeMap modeMap modeSrc
      if modeTgtDecl /= modeTgtExpected
        then Left "morphism: target mode does not match mode map"
        else Right ()
      let name = ObjName (rpmtSrcType decl)
      let mRef = lookupCtorRefForOwnerInTables src srcTables modeSrc name
      srcRef <-
        case mRef of
          Nothing -> Left "morphism: unknown source type in type map"
          Just ref -> Right ref
      srcParams <- lookupCtorSigForOwnerInTables src srcTables modeSrc srcRef
      (tmplParams, tyVarsTgt, tmVarsTgt) <- buildTypeTemplateParams tgt modeMap srcParams (rpmtParams decl)
      tgtExpr <- elabObjExpr tgt tyVarsTgt tmVarsTgt M.empty modeTgtDecl (rpmtTgtType decl)
      if objOwnerMode tgtExpr /= modeTgtDecl
        then Left ("morphism: target type expression mode mismatch (expected " <> rpmtTgtMode decl <> ")")
        else Right ()
      if M.member srcRef mp
        then Left "morphism: duplicate type mapping"
        else Right (M.insert srcRef (TypeTemplate tmplParams tgtExpr) mp)
    addGenMap src tgt ttSrc ttTgt tgtTables modeMap mor0 mp decl = do
      let modeSrc = ModeName (rpmgMode decl)
      ensureMode src modeSrc
      modeTgt <- lookupModeMap modeMap modeSrc
      ensureMode tgt modeTgt
      gen <- lookupGen src modeSrc (GenName (rpmgSrcGen decl))
      tyVarsTgt <- mapM (mapTyVarMode ttSrc ttTgt tgtTables mor0) (gdTyVars gen)
      tmVarsTgt <- mapM (mapTmVarSort ttSrc ttTgt tgtTables mor0) (gdTmVars gen)
      binderSigs0 <- buildBinderHoleSigs ttSrc ttTgt tgtTables mor0 gen
      (diag0, _) <- elabDiagExprWith env tgt modeTgt [] tyVarsTgt tmVarsTgt binderSigs0 BMUse True (rpmgRhs decl)
      let domSrc = gdPlainDom gen
      let codSrc = gdCod gen
      domTgt <- mapM (applyMorphismTyWithCaches ttSrc ttTgt tgtTables mor0) domSrc
      codTgt <- mapM (applyMorphismTyWithCaches ttSrc ttTgt tgtTables mor0) codSrc
      let rigidTy = S.fromList (map tmVarToObjVar tyVarsTgt)
      let rigidTm = S.fromList tmVarsTgt
      diag <- unifyBoundary ttTgt rigidTy rigidTm domTgt codTgt diag0
      let freeTy = freeObjVarsDiagram diag
      let allowedTy = S.fromList (map tmVarToObjVar tyVarsTgt)
      if S.isSubsetOf freeTy allowedTy
        then Right ()
        else Left "morphism: generator mapping uses undeclared type variables"
      let freeTm = freeTmVarsDiagram diag
      let allowedTm = S.fromList tmVarsTgt
      if S.isSubsetOf freeTm allowedTm
        then Right ()
        else Left "morphism: generator mapping uses undeclared term variables"
      let usedMetas = binderMetaVarsDiagram diag
      let allowedMetas = M.keysSet binderSigs0
      if S.isSubsetOf usedMetas allowedMetas
        then Right ()
        else Left "morphism: generator mapping uses undeclared binder holes"
      let key = (modeSrc, gdName gen)
      if M.member key mp
        then Left "morphism: duplicate generator mapping"
        else Right (M.insert key (GenImage diag binderSigs0) mp)
    buildBinderHoleSigs ttSrc ttTgt tgtTables mor gen =
      let slots = [ bs | InBinder bs <- gdDom gen ]
          holes = [ BinderMetaVar ("b" <> T.pack (show i)) | i <- [0 .. length slots - 1] ]
      in fmap M.fromList (mapM (mapOne ttSrc ttTgt tgtTables mor) (zip holes slots))
    mapOne ttSrc ttTgt tgtTables mor (hole, sig) = do
      tmCtx' <- mapM (applyMorphismTyWithCaches ttSrc ttTgt tgtTables mor) (bsTmCtx sig)
      dom' <- mapM (applyMorphismTyWithCaches ttSrc ttTgt tgtTables mor) (bsDom sig)
      cod' <- mapM (applyMorphismTyWithCaches ttSrc ttTgt tgtTables mor) (bsCod sig)
      pure (hole, sig { bsTmCtx = tmCtx', bsDom = dom', bsCod = cod' })
    -- no template restriction; any target type expression using only params is allowed
    ensureAllGenMapped src srcCtorTables mp = do
      let gens =
            [ (mode, gdName g)
            | (mode, table) <- M.toList (dGens src)
            , g <- M.elems table
            , not (isTypeDeclGenNameInTables src srcCtorTables mode (ObjName (renderGenName (gdName g))))
            ]
      case [ (m, g) | (m, g) <- gens, M.notMember (m, g) mp ] of
        [] -> Right ()
        missing ->
          Left
            ( "morphism: missing generator mapping: "
                <> T.intercalate
                  ", "
                  [ renderModeName m <> "." <> renderGenName g
                  | (m, g) <- missing
                  ]
            )

parsePolicy :: Text -> Either Text RewritePolicy
parsePolicy name =
  case name of
    "UseOnlyComputationalLR" -> Right UseOnlyComputationalLR
    "UseStructuralAsBidirectional" -> Right UseStructuralAsBidirectional
    "UseAllOriented" -> Right UseAllOriented
    _ -> Left ("Unknown policy: " <> name)

parseMorphismCheck :: Text -> Either Text MorphismCheck
parseMorphismCheck name =
  case name of
    "all" -> Right CheckAll
    "structural" -> Right CheckStructural
    "none" -> Right CheckNone
    other ->
      Left
        ( "Unknown morphism check mode: "
            <> other
            <> " (expected: all | structural | none)"
        )

morphismBudget :: SearchBudget -> RawPolyMorphism -> SearchBudget
morphismBudget budgetDefault raw =
  let depth = max 0 (maybe (sbMaxDepth budgetDefault) id (rpmMaxDepth raw))
      states = max 1 (maybe (sbMaxStates budgetDefault) id (rpmMaxStates raw))
      timeoutMs = max 0 (maybe (sbTimeoutMs budgetDefault) id (rpmTimeoutMs raw))
   in budgetDefault
        { sbMaxDepth = depth
        , sbMaxStates = states
        , sbTimeoutMs = timeoutMs
        }
