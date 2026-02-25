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

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import qualified Data.Set as S
import qualified Data.List as L
import Data.Char (isAlphaNum)
import Data.Maybe (catMaybes, fromMaybe)
import Control.Monad (foldM, when)
import Strat.DSL.AST (RawPolyMorphism(..), RawPolyMorphismItem(..), RawPolyTypeMap(..), RawPolyGenMap(..), RawPolyModeMap(..), RawPolyModalityMap(..), RawPolyAttrSortMap(..))
import Strat.Poly.DSL.AST
import Strat.Poly.Doctrine
import Strat.Poly.Diagram
import Strat.Poly.Graph (emptyDiagram, freshPort, setPortLabel, addEdgePayload, Edge(..), EdgeId(..), PortId(..), EdgePayload(..), BinderArg(..), BinderMetaVar(..), validateDiagram, diagramPortObj)
import Strat.Poly.ModeTheory
import Strat.Poly.Names
import Strat.Poly.Obj
import Strat.Poly.ObjClassifier (modeClassifierMode, modeUniverseObj)
import Strat.Poly.ObjResolve
  ( resolveTypeRefInClassifierInTables
  , resolveTypeRefInClassifierMaybeInTables
  )
import qualified Strat.Poly.UnifyObj as U
import Strat.Poly.TypeTheory (TypeTheory(..), TypeParamSig(..), TmFunSig(..))
import Strat.Poly.DefEq (normalizeObjDeep, termExprToDiagramChecked, defEqTermDiagram)
import Strat.Poly.Attr
import Strat.Poly.Morphism
import Strat.Poly.ModAction (ActionSemanticsResult(..), applyModExpr, validateActionSemanticsWithBudgetResult)
import Strat.Poly.CompObligations (installGeneratedCompObligations, isGeneratedCompObligation)
import Strat.Poly.BeckChevalleyObligations (installGeneratedBeckChevalleyObligations, isGeneratedBeckChevalleyObligation)
import Strat.Poly.Slots
  ( Slot(..)
  , SlotId(..)
  , SlotKind(..)
  , SlotSig(..)
  , extractDoctrineSlotsWithTables
  )
import Strat.Frontend.Env (ModuleEnv(..), TermDef(..))
import Strat.Frontend.Coerce (coerceDiagramTo)
import Strat.Poly.Cell2 (Cell2(..))
import Strat.Common.Rules (RewritePolicy(..))
import Strat.Poly.TermExpr (TermExpr(..))
import Strat.Poly.Rewrite (rulesFromPolicy)
import Strat.Poly.Normalize (NormalizationStatus(..), autoJoinProof, normalize)
import Strat.Poly.DiagramIso (diagramIsoEq)
import Strat.Poly.Proof
  ( JoinProof(..)
  , RewritePath(..)
  , SearchBudget(..)
  , SearchLimit
  , SearchOutcome(..)
  , defaultSearchBudget
  , renderSearchLimit
  , checkJoinProof
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
        Just m -> Left ("morphism: duplicate mode mapping for " <> renderModeName m)
        Nothing -> Right ()
      let explicit = M.fromList pairs
      let missing = [ m | m <- M.keys srcModes, M.notMember m explicit, M.notMember m tgtModes ]
      case missing of
        (m:_) -> Left ("morphism: missing mode mapping for " <> renderModeName m)
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
        renderModeName (ModeName name) = name
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
      let rigidTy = S.fromList tyVarsTgt
      let rigidTm = S.fromList tmVarsTgt
      diag <- unifyBoundary ttTgt rigidTy rigidTm domTgt codTgt diag0
      let freeTy = freeObjVarsDiagram diag
      let allowedTy = S.fromList tyVarsTgt
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
      let isCompSupport mode gName =
            case M.lookup mode (mtClassifiedBy (dModes src)) >>= cdComp of
              Just comp ->
                gName == compCtxExt comp
                  || gName == compVar comp
                  || gName == compReindex comp
              Nothing -> False
      let gens =
            [ (mode, gdName g)
            | (mode, table) <- M.toList (dGens src)
            , g <- M.elems table
            , not (isCompSupport mode (gdName g))
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

data ElabState = ElabState
  { esDoc :: Doctrine
  , esPendingClass :: [(ModeName, RawClassifiedByDecl)]
  , esPendingComp :: [RawCompDecl]
  }

elabPolyDoctrine :: ModuleEnv -> RawPolyDoctrine -> Either Text Doctrine
elabPolyDoctrine env raw = fst <$> elabPolyDoctrineWithBudgetResult defaultSearchBudget env raw

elabPolyDoctrineWithBudget :: SearchBudget -> ModuleEnv -> RawPolyDoctrine -> Either Text Doctrine
elabPolyDoctrineWithBudget budget env raw =
  fst <$> elabPolyDoctrineWithBudgetResult budget env raw

elabPolyDoctrineWithBudgetResult :: SearchBudget -> ModuleEnv -> RawPolyDoctrine -> Either Text (Doctrine, Int)
elabPolyDoctrineWithBudgetResult budget env raw = do
  base <- case rpdExtends raw of
    Nothing -> Right Nothing
    Just name ->
      case M.lookup name (meDoctrines env) of
        Nothing -> Left ("Unknown doctrine: " <> name)
        Just doc -> Right (Just doc)
  let start = ElabState { esDoc = seedDoctrine (rpdName raw) base, esPendingClass = [], esPendingComp = [] }
  st <- foldM (elabPolyItem env) start (rpdItems raw)
  doc0 <- applyPendingDeclarations st
  docComp <- installGeneratedCompObligations doc0
  doc <- installGeneratedBeckChevalleyObligations docComp
  validateDoctrine doc
  actionProofCount <- validateActionSemanticsProofCount budget doc
  compProofCount <- validateCompSemanticsProofCount budget env doc
  bcProofCount <- validateBCSemanticsProofCount budget env doc
  pure (doc, actionProofCount + compProofCount + bcProofCount)

elabPolyDoctrineFromBaseWithBudgetResult
  :: SearchBudget
  -> ModuleEnv
  -> Doctrine
  -> RawPolyDoctrine
  -> Either Text (Doctrine, Int)
elabPolyDoctrineFromBaseWithBudgetResult budget env baseDoc raw = do
  let start = ElabState { esDoc = seedDoctrine (rpdName raw) (Just baseDoc), esPendingClass = [], esPendingComp = [] }
  st <- foldM (elabPolyItem env) start (rpdItems raw)
  doc0 <- applyPendingDeclarations st
  docComp <- installGeneratedCompObligations doc0
  doc <- installGeneratedBeckChevalleyObligations docComp
  validateDoctrine doc
  actionProofCount <- validateActionSemanticsProofCount budget doc
  compProofCount <- validateCompSemanticsProofCount budget env doc
  bcProofCount <- validateBCSemanticsProofCount budget env doc
  pure (doc, actionProofCount + compProofCount + bcProofCount)

validateActionSemanticsProofCount :: SearchBudget -> Doctrine -> Either Text Int
validateActionSemanticsProofCount budget doc = do
  result <- validateActionSemanticsWithBudgetResult budget doc
  case result of
    ActionSemanticsProved proofs ->
      Right (length proofs)
    ActionSemanticsUndecided label lim ->
      Left
        ( "validateDoctrine: action semantics undecided for "
            <> label
            <> " ("
            <> renderSearchLimit lim
            <> ")"
        )

validateCompSemanticsProofCount :: SearchBudget -> ModuleEnv -> Doctrine -> Either Text Int
validateCompSemanticsProofCount budget env doc = do
  let generated = [obl | obl <- dObligations doc, isGeneratedCompObligation obl]
  if null generated
    then Right 0
    else do
      let schemaDoc = doc { dObligations = generated }
      identityMor <- identityMorphismFor doc
      result <- checkImplementsObligationsWithBudget budget env doc identityMor schemaDoc
      case result of
        ImplementsCheckProved proofs ->
          Right (length proofs)
        ImplementsCheckUndecided label lim ->
          Left
            ( "validateDoctrine: comprehension semantics undecided for "
                <> label
                <> " ("
                <> renderSearchLimit lim
                <> ")"
            )

validateBCSemanticsProofCount :: SearchBudget -> ModuleEnv -> Doctrine -> Either Text Int
validateBCSemanticsProofCount budget env doc = do
  let generated = [obl | obl <- dObligations doc, isGeneratedBeckChevalleyObligation obl]
  if null generated
    then Right 0
    else do
      let schemaDoc = doc { dObligations = generated }
      identityMor <- identityMorphismFor doc
      result <- checkImplementsObligationsWithBudget budget env doc identityMor schemaDoc
      case result of
        ImplementsCheckProved proofs ->
          Right (length proofs)
        ImplementsCheckUndecided label lim ->
          Left
            ( "validateDoctrine: Beck-Chevalley semantics undecided for "
                <> label
                <> " ("
                <> renderSearchLimit lim
                <> ")"
            )

identityMorphismFor :: Doctrine -> Either Text Morphism
identityMorphismFor doc = do
  genMap <- mkIdentityGenMap doc
  pure
    Morphism
      { morName = "__generated.comp.identity"
      , morSrc = doc
      , morTgt = doc
      , morIsCoercion = True
      , morModeMap = modeMap
      , morModMap = modMap
      , morAttrSortMap = attrSortMap
      , morTypeMap = M.empty
      , morGenMap = genMap
      , morCheck = CheckNone
      , morPolicy = UseStructuralAsBidirectional
      }
  where
    modeMap =
      M.fromList
        [ (m, m)
        | m <- M.keys (mtModes (dModes doc))
        ]
    modMap =
      M.fromList
        [ ( name
          , ModExpr
              { meSrc = mdSrc decl
              , meTgt = mdTgt decl
              , mePath = [name]
              }
          )
        | (name, decl) <- M.toList (mtDecls (dModes doc))
        ]
    attrSortMap =
      M.fromList
        [ (s, s)
        | s <- M.keys (dAttrSorts doc)
        ]

mkIdentityGenMap :: Doctrine -> Either Text (M.Map (ModeName, GenName) GenImage)
mkIdentityGenMap doc = do
  ctorTables <- deriveCtorTables doc
  fmap M.fromList (mapM mkOne (allNonTypeGens ctorTables))
  where
    allNonTypeGens ctorTables =
      [ (mode, gd)
      | (mode, table) <- M.toList (dGens doc)
      , gd <- M.elems table
      , not (isTypeDeclGenNameInTables doc ctorTables mode (ObjName (renderGenName (gdName gd))))
      ]

    mkOne (mode, gd) = do
      diag <- mkForGenDiag mode gd
      let binderSlots = [ bs | InBinder bs <- gdDom gd ]
      let holes = [ BinderMetaVar ("for_gen_b" <> T.pack (show i)) | i <- [0 .. length binderSlots - 1] ]
      let binderSigs = M.fromList (zip holes binderSlots)
      pure ((mode, gdName gd), GenImage diag binderSigs)

seedDoctrine :: Text -> Maybe Doctrine -> Doctrine
seedDoctrine name base =
  case base of
    Nothing -> Doctrine
      { dName = name
      , dModes = emptyModeTheory
      , dAcyclicModes = S.empty
      , dAttrSorts = M.empty
      , dGens = M.empty
      , dCells2 = []
      , dActions = M.empty
      , dObligations = []
      }
    Just doc -> doc { dName = name, dAttrSorts = dAttrSorts doc }

applyPendingDeclarations :: ElabState -> Either Text Doctrine
applyPendingDeclarations st = do
  doc <- applyPendingClassifications st
  applyPendingComprehensions st doc

applyPendingClassifications :: ElabState -> Either Text Doctrine
applyPendingClassifications st =
  foldM addOne (esDoc st) (esPendingClass st)
  where
    addOne doc (mode, rawClass) = do
      ensureMode doc mode
      let classifier = ModeName (rcdClassifier rawClass)
      ensureMode doc classifier
      ctorTables <- deriveCtorTablesForElab doc
      let existingUniverse =
            case M.lookup mode (mtClassifiedBy (dModes doc)) of
              Just existing -> Just (cdUniverse existing)
              Nothing -> Nothing
      universe <-
        case elabObjExprWithTables doc ctorTables [] [] M.empty classifier (rcdUniverse rawClass) of
          Right u -> Right u
          Left err ->
            case existingUniverse of
              Just u
                | not (isPendingUniverseObj u) ->
                    Right u
              _ -> Left err
      if objOwnerMode universe == classifier
        then Right ()
        else Left "classifiedBy universe mode mismatch"
      let decl =
            ClassificationDecl
              { cdClassifier = classifier
              , cdUniverse = universe
              , cdTag = rcdTag rawClass
              , cdComp =
                  case M.lookup mode (mtClassifiedBy (dModes doc)) of
                    Just existing -> cdComp existing
                    Nothing -> Nothing
              }
      mt' <-
        case M.lookup mode (mtClassifiedBy (dModes doc)) of
          Nothing ->
            addClassification mode decl (dModes doc)
          Just existing ->
            if cdClassifier existing == classifier
              then
                Right
                  (dModes doc)
                    { mtClassifiedBy = M.insert mode decl (mtClassifiedBy (dModes doc))
                    }
              else Left "classifiedBy classifier mismatch for pending mode"
      Right doc { dModes = mt' }

applyPendingComprehensions :: ElabState -> Doctrine -> Either Text Doctrine
applyPendingComprehensions st doc0 = do
  ctorTables <- deriveCtorTables doc0
  foldM (addOne ctorTables) doc0 (esPendingComp st)
  where
    addOne ctorTables doc rawComp = do
      let mode = ModeName (rcmpMode rawComp)
      ensureMode doc mode
      classDecl <-
        case M.lookup mode (mtClassifiedBy (dModes doc)) of
          Nothing -> Left "comprehension declaration requires classifiedBy on the mode"
          Just decl -> Right decl
      let ctxExtName = GenName (rcmpCtxExt rawComp)
      let varName = GenName (rcmpVar rawComp)
      let reindexName = GenName (rcmpReindex rawComp)
      ensureGen mode ctxExtName doc
      ensureGen mode varName doc
      ensureGen mode reindexName doc
      ensureNonType ctorTables mode ctxExtName doc
      ensureNonType ctorTables mode varName doc
      ensureNonType ctorTables mode reindexName doc
      let compDecl =
            CompDecl
              { compCtxExt = ctxExtName
              , compVar = varName
              , compReindex = reindexName
              }
      case cdComp classDecl of
        Nothing ->
          let classDecl' = classDecl { cdComp = Just compDecl }
              mt' = (dModes doc) { mtClassifiedBy = M.insert mode classDecl' (mtClassifiedBy (dModes doc)) }
           in Right doc { dModes = mt' }
        Just existing
          | existing == compDecl -> Right doc
          | otherwise -> Left "duplicate comprehension declaration for mode"

    ensureGen mode genName doc =
      case M.lookup mode (dGens doc) >>= M.lookup genName of
        Just _ -> Right ()
        Nothing ->
          Left
            ( "comprehension declaration references unknown generator "
                <> renderMode mode
                <> "."
                <> renderGen genName
            )

    ensureNonType ctorTables mode genName doc =
      do
        let isCtor =
              isTypeDeclGenNameInTables
                doc
                ctorTables
                mode
                (ObjName (renderGen genName))
        if isCtor
        then
          Left
            ( "comprehension declaration expects term generator but got constructor-like generator "
                <> renderMode mode
                <> "."
                <> renderGen genName
            )
        else Right ()

    renderMode (ModeName n) = n
    renderGen (GenName n) = n

elabPolyItem :: ModuleEnv -> ElabState -> RawPolyItem -> Either Text ElabState
elabPolyItem env st item =
  let doc = esDoc st
   in
  case item of
    RPMode decl -> do
      let mode = ModeName (rmdName decl)
      mt0 <- addMode mode (dModes doc)
      mt' <-
        case rmdClassifiedBy decl of
          Nothing -> Right mt0
          Just rawClass -> do
            let classifier = ModeName (rcdClassifier rawClass)
            addClassification
              mode
              ClassificationDecl
                { cdClassifier = classifier
                , cdUniverse = pendingClassUniverse classifier (rcdUniverse rawClass)
                , cdTag = rcdTag rawClass
                , cdComp = Nothing
                }
              mt0
      let acyclic' =
            if rmdAcyclic decl
              then S.insert mode (dAcyclicModes doc)
              else dAcyclicModes doc
      let pending' =
            case rmdClassifiedBy decl of
              Nothing -> esPendingClass st
              Just rawClass -> esPendingClass st <> [(mode, rawClass)]
      pure
        st
          { esDoc = doc { dModes = mt', dAcyclicModes = acyclic' }
          , esPendingClass = pending'
          }
    RPComprehension compDecl ->
      pure st { esPendingComp = esPendingComp st <> [compDecl] }
    RPClassifierLift decl -> do
      let modName = ModName (rclModality decl)
      liftExpr <- elabRawModExpr (dModes doc) (rclLift decl)
      mt' <- addClassifierLift modName liftExpr (dModes doc)
      pure st { esDoc = doc { dModes = mt' } }
    RPModality decl -> do
      let modDecl =
            ModDecl
              { mdName = ModName (rmodName decl)
              , mdSrc = ModeName (rmodSrc decl)
              , mdTgt = ModeName (rmodTgt decl)
              }
      mt' <- addModDecl modDecl (dModes doc)
      pure st { esDoc = doc { dModes = mt' } }
    RPModEq decl -> do
      lhs <- elabRawModExpr (dModes doc) (rmeLHS decl)
      rhs <- elabRawModExpr (dModes doc) (rmeRHS decl)
      mt' <- addModEqn (ModEqn lhs rhs) (dModes doc)
      pure st { esDoc = doc { dModes = mt' } }
    RPModTransform decl ->
      do
        doc' <- elabModTransformDecl doc decl
        pure st { esDoc = doc' }
    RPAction decl -> do
      let modName = ModName (radModName decl)
      modDecl <-
        case M.lookup modName (mtDecls (dModes doc)) of
          Nothing -> Left "action references unknown modality"
          Just d -> Right d
      let srcMode = mdSrc modDecl
      let tgtMode = mdTgt modDecl
      imgs <- mapM (elabActionImage env doc tgtMode) (radGenMap decl)
      let action =
            ModAction
              { maMod = modName
              , maGenMap = M.fromList [ ((srcMode, g), d) | (g, d) <- imgs ]
              , maPolicy = UseStructuralAsBidirectional
              }
      if M.member modName (dActions doc)
        then Left "duplicate action declaration"
        else pure st { esDoc = doc { dActions = M.insert modName action (dActions doc) } }
    RPObligation decl -> do
      let mode = ModeName (rodMode decl)
      ensureMode doc mode
      if rodForGen decl
        then do
          if null (rodVars decl) && null (rodDom decl) && null (rodCod decl)
            then pure ()
            else Left "obligation for_gen does not accept explicit vars or boundary signature"
          validateObligationExprMode doc mode True (rodLHS decl)
          validateObligationExprMode doc mode True (rodRHS decl)
          let obl =
                ObligationDecl
                  { obName = rodName decl
                  , obMode = mode
                  , obForGen = True
                  , obForGenName = Nothing
                  , obGenerated = False
                  , obTyVars = []
                  , obTmVars = []
                  , obDom = []
                  , obCod = []
                  , obLHSExpr = rodLHS decl
                  , obRHSExpr = rodRHS decl
                  , obPolicy = UseStructuralAsBidirectional
                  }
          pure st { esDoc = doc { dObligations = dObligations doc <> [obl] } }
        else do
          (tyVars, tmVars, _sigParams) <- elabParamDecls doc mode (rodVars decl)
          dom <- elabContext doc mode tyVars tmVars M.empty (rodDom decl)
          cod <- elabContext doc mode tyVars tmVars M.empty (rodCod decl)
          validateObligationExprMode doc mode False (rodLHS decl)
          validateObligationExprMode doc mode False (rodRHS decl)
          let obl =
                ObligationDecl
                  { obName = rodName decl
                  , obMode = mode
                  , obForGen = False
                  , obForGenName = Nothing
                  , obGenerated = False
                  , obTyVars = tyVars
                  , obTmVars = tmVars
                  , obDom = dom
                  , obCod = cod
                  , obLHSExpr = rodLHS decl
                  , obRHSExpr = rodRHS decl
                  , obPolicy = UseStructuralAsBidirectional
                  }
          pure st { esDoc = doc { dObligations = dObligations doc <> [obl] } }
    RPAttrSort decl -> do
      let sortName = AttrSort (rasName decl)
      litKind <- mapM parseAttrLitKind (rasKind decl)
      if M.member sortName (dAttrSorts doc)
        then Left "duplicate attribute sort name"
        else do
          let sortDecl = AttrSortDecl { asName = sortName, asLitKind = litKind }
          pure st { esDoc = doc { dAttrSorts = M.insert sortName sortDecl (dAttrSorts doc) } }
    RPGen decl -> do
      let mode = ModeName (rpgMode decl)
      ensureMode doc mode
      let gname = GenName (rpgName decl)
      (tyVars, tmVars, params) <- elabParamDecls doc mode (rpgVars decl)
      let table0 = M.findWithDefault M.empty mode (dGens doc)
      if M.member gname table0
        then Left "duplicate generator name"
        else Right ()
      let provisional =
            GenDecl
              { gdName = gname
              , gdMode = mode
              , gdTyVars = tyVars
              , gdTmVars = tmVars
              , gdParams = params
              , gdDom = []
              , gdCod = [provisionalCtorSort doc mode]
              , gdAttrs = []
              }
      let docForElab =
            doc
              { dGens = M.insert mode (M.insert gname provisional table0) (dGens doc)
              }
      attrs <- mapM (resolveAttrField doc) (rpgAttrs decl)
      ensureDistinct "duplicate generator attribute field name" (map fst attrs)
      dom <- elabInputShapes docForElab mode tyVars tmVars (rpgDom decl)
      cod <- elabContext docForElab mode tyVars tmVars M.empty (rpgCod decl)
      let gen = GenDecl
            { gdName = gname
            , gdMode = mode
            , gdTyVars = tyVars
            , gdTmVars = tmVars
            , gdParams = params
            , gdDom = dom
            , gdCod = cod
            , gdAttrs = attrs
            }
      let table' = M.insert gname gen table0
      let gens' = M.insert mode table' (dGens doc)
      pure st { esDoc = doc { dGens = gens' } }
    RPData decl -> do
      let modeName = rpdTyMode decl
      let ownerMode = ModeName modeName
      ensureMode doc ownerMode
      let classifierMode = modeClassifierMode (dModes doc) ownerMode
      ensureMode doc classifierMode
      universe <-
        case modeUniverseObj (dModes doc) ownerMode of
          Nothing ->
            Left
              ( "data: mode "
                  <> modeName
                  <> " is missing a classifiedBy universe"
              )
          Just u -> Right u
      let ctorNames = map rpdCtorName (rpdCtors decl)
      ensureDistinct "data: duplicate constructor name" ctorNames
      let typeName = rpdTyName decl
      let existingOwner = M.findWithDefault M.empty ownerMode (dGens doc)
      let existingClassifier = M.findWithDefault M.empty classifierMode (dGens doc)
      case [c | c <- ctorNames, M.member (GenName c) existingOwner] of
        (c:_) -> Left ("data: constructor name conflicts with generator " <> c)
        [] -> Right ()
      if M.member (GenName typeName) existingClassifier
        then Left ("data: type constructor name conflicts with classifier generator " <> typeName)
        else Right ()
      (tyVars, tmVars, params) <- elabParamDecls doc classifierMode (map RPDType (rpdTyVars decl))
      let typeCtorGen =
            GenDecl
              { gdName = GenName typeName
              , gdMode = classifierMode
              , gdTyVars = tyVars
              , gdTmVars = tmVars
              , gdParams = params
              , gdDom = []
              , gdCod = [universe]
              , gdAttrs = []
              }
      let classifierTable' = M.insert (gdName typeCtorGen) typeCtorGen existingClassifier
      let doc' =
            doc
              { dGens = M.insert classifierMode classifierTable' (dGens doc)
              }
      let st' = st { esDoc = doc' }
      let ctors = map (mkCtor modeName typeName (rpdTyVars decl)) (rpdCtors decl)
      foldM (elabPolyItem env) st' (map RPGen ctors)
    RPRule decl -> do
      let mode = ModeName (rprMode decl)
      ensureMode doc mode
      (ruleTyVars, ruleTmVars, _sigParams) <- elabParamDecls doc mode (rprVars decl)
      dom <- elabContext doc mode ruleTyVars ruleTmVars M.empty (rprDom decl)
      cod <- elabContext doc mode ruleTyVars ruleTmVars M.empty (rprCod decl)
      (lhs, binderSigs) <- withRule (elabRuleLHS env doc mode ruleTyVars ruleTmVars (rprLHS decl))
      rhs <- withRule (elabRuleRHS env doc mode ruleTyVars ruleTmVars binderSigs (rprRHS decl))
      let rigidTy = S.fromList ruleTyVars
      let rigidTm = S.fromList ruleTmVars
      tt <- doctrineTypeTheory doc
      lhs' <- unifyBoundary tt rigidTy rigidTm dom cod lhs
      rhs' <- unifyBoundary tt rigidTy rigidTm dom cod rhs
      let free = S.union (freeObjVarsDiagram lhs') (freeObjVarsDiagram rhs')
      let allowed = S.fromList ruleTyVars
      if S.isSubsetOf free allowed
        then pure ()
        else Left ("rule " <> rprName decl <> ": unresolved type variables")
      let lhsAttrVars = freeAttrVarsDiagram lhs'
      let rhsAttrVars = freeAttrVarsDiagram rhs'
      if S.isSubsetOf rhsAttrVars lhsAttrVars
        then pure ()
        else Left ("rule " <> rprName decl <> ": RHS introduces fresh attribute variables")
      let cell = Cell2
            { c2Name = rprName decl
            , c2Class = rprClass decl
            , c2Orient = rprOrient decl
            , c2TyVars = ruleTyVars
            , c2TmVars = ruleTmVars
            , c2LHS = lhs'
            , c2RHS = rhs'
            }
      pure st { esDoc = doc { dCells2 = dCells2 doc <> [cell] } }
      where
        withRule action =
          case action of
            Left err -> Left ("rule " <> rprName decl <> ": " <> err)
            Right x -> Right x

elabModTransformDecl :: Doctrine -> RawModTransformDecl -> Either Text Doctrine
elabModTransformDecl doc decl = do
  fromMe <- elabRawModExpr (dModes doc) (rmtFrom decl)
  toMe <- elabRawModExpr (dModes doc) (rmtTo decl)
  if meSrc fromMe == meSrc toMe && meTgt fromMe == meTgt toMe
    then Right ()
    else Left "mod_transform: source/target mismatch between transform sides"
  let witnessText = fromMaybe (rmtName decl) (rmtWitness decl)
  let witness = GenName witnessText
  let witnessMode = meTgt fromMe
  witnessGen <- lookupGen doc witnessMode witness
  checkModTransformWitness doc fromMe toMe witnessGen
  let transformDecl =
        ModTransformDecl
          { mtdName = ModTransformName (rmtName decl)
          , mtdFrom = fromMe
          , mtdTo = toMe
          , mtdWitness = witness
          }
  mt' <- addModTransformDecl transformDecl (dModes doc)
  pure doc { dModes = mt' }

ensureDistinct :: Text -> [Text] -> Either Text ()
ensureDistinct label names =
  let set = S.fromList names
  in if S.size set == length names then Right () else Left label

elabRawModExpr :: ModeTheory -> RawModExpr -> Either Text ModExpr
elabRawModExpr mt raw =
  case raw of
    RMId modeName -> do
      let mode = ModeName modeName
      if M.member mode (mtModes mt)
        then Right ModExpr { meSrc = mode, meTgt = mode, mePath = [] }
        else Left ("unknown mode in modality expression: " <> modeName)
    RMComp toks -> do
      path <- mapM requireModName (reverse toks)
      case path of
        [] -> Left "empty modality expression"
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
            else Left ("unknown modality in expression: " <> tok)
    requireDecl name =
      case M.lookup name (mtDecls mt) of
        Nothing -> Left "unknown modality"
        Just decl -> Right decl
    step cur name = do
      decl <- requireDecl name
      if mdSrc decl == cur
        then Right (mdTgt decl)
        else Left "modality composition type mismatch"

parseAttrLitKind :: Text -> Either Text AttrLitKind
parseAttrLitKind name =
  case name of
    "int" -> Right LKInt
    "string" -> Right LKString
    "bool" -> Right LKBool
    _ -> Left "unknown attribute literal kind"

rpdCtorName :: RawPolyCtorDecl -> Text
rpdCtorName = rpcName

mkCtor :: Text -> Text -> [RawTyVarDecl] -> RawPolyCtorDecl -> RawPolyGenDecl
mkCtor modeName tyName vars ctor =
  let typeRef = RawTypeRef { rtrMode = Nothing, rtrName = tyName }
      args = map (RPTVar . rtvName) vars
      cod = [RPTCon typeRef args]
  in RawPolyGenDecl
      { rpgName = rpcName ctor
      , rpgVars = map RPDType vars
      , rpgAttrs = []
      , rpgDom = map RIPort (rpcArgs ctor)
      , rpgCod = cod
      , rpgMode = modeName
      }

resolveAttrField :: Doctrine -> (Text, Text) -> Either Text (AttrName, AttrSort)
resolveAttrField doc (fieldName, sortName) = do
  let sortRef = AttrSort sortName
  if M.member sortRef (dAttrSorts doc)
    then Right (fieldName, sortRef)
    else Left "unknown attribute sort"

elabActionImage :: ModuleEnv -> Doctrine -> ModeName -> (Text, RawDiagExpr) -> Either Text (GenName, Diagram)
elabActionImage env doc tgtMode (genName, rhs) = do
  d <- elabDiagExpr env doc tgtMode [] rhs
  pure (GenName genName, d)

validateObligationExprMode :: Doctrine -> ModeName -> Bool -> RawOblExpr -> Either Text ()
validateObligationExprMode doc mode allowGen = go mode
  where
    rootMode = mode

    go expected expr =
      case expr of
        ROEDiag _ ->
          Right ()
        ROEMap rawMe inner -> do
          me <- elabRawModExpr (dModes doc) rawMe
          if meTgt me == expected
            then go (meSrc me) inner
            else Left "obligation map: mapped diagram mode does not match surrounding expression mode"
        ROEGen ->
          if allowGen && expected == rootMode
            then Right ()
            else
              if allowGen
                then Left "obligation: @gen is only valid at the obligation mode"
                else Left "obligation: @gen is only valid in for_gen obligations"
        ROELiftDom _ ->
          if allowGen && expected == rootMode
            then Right ()
            else
              if allowGen
                then Left "obligation: lift_dom is only valid at the obligation mode"
                else Left "obligation: lift_dom is only valid in for_gen obligations"
        ROELiftCod _ ->
          if allowGen && expected == rootMode
            then Right ()
            else
              if allowGen
                then Left "obligation: lift_cod is only valid at the obligation mode"
                else Left "obligation: lift_cod is only valid in for_gen obligations"
        ROEComp a b ->
          go expected a >> go expected b
        ROETensor a b ->
          go expected a >> go expected b

data ImplementsCheckResult
  = ImplementsCheckProved [(Text, ImplementsProof)]
  | ImplementsCheckUndecided Text SearchLimit
  deriving (Eq, Show)

data ImplementsProof
  = ImplementsProofJoin JoinProof
  | ImplementsProofDefEq
  deriving (Eq, Show)

checkImplementsObligationsWithBudget :: SearchBudget -> ModuleEnv -> Doctrine -> Morphism -> Doctrine -> Either Text ImplementsCheckResult
checkImplementsObligationsWithBudget budget env tgtDoc morph ifaceDoc = do
  ttTgt <- doctrineTypeTheory tgtDoc
  ttSrc <- doctrineTypeTheory (morSrc morph)
  let tgtCtorTables = ttCtorTables ttTgt
  slotsByGen <- extractDoctrineSlotsWithTables tgtDoc tgtCtorTables
  checkObligations ttSrc ttTgt tgtCtorTables slotsByGen (dObligations ifaceDoc)
  where
    checkObligations _ _ _ _ [] = Right (ImplementsCheckProved [])
    checkObligations ttSrc ttTgt tgtCtorTables slotsByGen (obl:rest) = do
      result <- checkOne ttSrc ttTgt tgtCtorTables slotsByGen obl
      case result of
        ImplementsCheckUndecided{} -> Right result
        ImplementsCheckProved proofs -> do
          restResult <- checkObligations ttSrc ttTgt tgtCtorTables slotsByGen rest
          case restResult of
            ImplementsCheckUndecided{} -> Right restResult
            ImplementsCheckProved restProofs ->
              Right (ImplementsCheckProved (proofs <> restProofs))

    generatedCompRules = rulesFromPolicy UseOnlyComputationalLR (dCells2 tgtDoc)

    checkOne ttSrc ttTgt tgtCtorTables slotsByGen obl
      | obForGen obl = checkForGen ttSrc ttTgt tgtCtorTables slotsByGen obl
      | otherwise = checkPlain ttSrc ttTgt tgtCtorTables obl

    checkPlain ttSrc ttTgt tgtCtorTables obl = do
      tyVarsTgt <- mapM (mapObligationTyVar ttSrc ttTgt tgtCtorTables morph) (obTyVars obl)
      tmVarsTgt <- mapM (mapObligationTmVar ttSrc ttTgt tgtCtorTables morph) (obTmVars obl)
      lhs0 <- evalObligationExprMapped ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph (obMode obl) (obTyVars obl) (obTmVars obl) (obLHSExpr obl)
      rhs0 <- evalObligationExprMapped ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph (obMode obl) (obTyVars obl) (obTmVars obl) (obRHSExpr obl)
      domTgt <- mapM (applyMorphismTyWithCaches ttSrc ttTgt tgtCtorTables morph) (obDom obl)
      codTgt <- mapM (applyMorphismTyWithCaches ttSrc ttTgt tgtCtorTables morph) (obCod obl)
      let rigidTy = S.fromList tyVarsTgt
      let rigidTm = S.fromList tmVarsTgt
      lhs <- unifyBoundary ttTgt rigidTy rigidTm domTgt codTgt lhs0
      rhs <- unifyBoundary ttTgt rigidTy rigidTm domTgt codTgt rhs0
      let rules = rulesFromPolicy (obPolicy obl) (dCells2 tgtDoc)
      checkObligationJoin ttTgt rules (obGenerated obl) (obName obl) lhs rhs

    checkForGen ttSrc ttTgt tgtCtorTables slotsByGen obl = do
      modeTgt <- applyMorphismMode morph (obMode obl)
      gens <- resolveForGenTargets tgtCtorTables modeTgt obl
      checkForGens ttSrc ttTgt tgtCtorTables slotsByGen modeTgt obl gens

    checkForGens _ _ _ _ _ _ [] = Right (ImplementsCheckProved [])
    checkForGens ttSrc ttTgt tgtCtorTables slotsByGen modeTgt obl (gen:rest) = do
      result <- checkForGenOne ttSrc ttTgt tgtCtorTables slotsByGen modeTgt obl gen
      case result of
        ImplementsCheckUndecided{} -> Right result
        ImplementsCheckProved proofs -> do
          restResult <- checkForGens ttSrc ttTgt tgtCtorTables slotsByGen modeTgt obl rest
          case restResult of
            ImplementsCheckUndecided{} -> Right restResult
            ImplementsCheckProved restProofs ->
              Right (ImplementsCheckProved (proofs <> restProofs))

    checkForGenOne ttSrc ttTgt tgtCtorTables slotsByGen modeTgt obl gen = do
      genDiag <- mkForGenDiag modeTgt gen
      lhs0 <- evalObligationExprForGen ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph (obMode obl) (gdTyVars gen) (gdTmVars gen) genDiag (obLHSExpr obl)
      rhs0 <- evalObligationExprForGen ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph (obMode obl) (gdTyVars gen) (gdTmVars gen) genDiag (obRHSExpr obl)
      dom <- diagramDom genDiag
      cod <- diagramCod genDiag
      let rigidTy = S.fromList (gdTyVars gen)
      let rigidTm = S.fromList (gdTmVars gen)
      lhs <- unifyBoundary ttTgt rigidTy rigidTm dom cod lhs0
      rhs <- unifyBoundary ttTgt rigidTy rigidTm dom cod rhs0
      let rules = rulesFromPolicy (obPolicy obl) (dCells2 tgtDoc)
      let label = obName obl <> "[" <> renderGenName (gdName gen) <> "]"
      generatedSlotOutcome <- checkGeneratedSlot ttTgt slotsByGen modeTgt gen obl label lhs rhs
      case generatedSlotOutcome of
        Just out -> Right out
        Nothing -> checkObligationJoin ttTgt rules (obGenerated obl) label lhs rhs

    resolveForGenTargets tgtCtorTables modeTgt obl =
      case obForGenName obl of
        Nothing -> Right allModeGens
        Just srcGenName -> do
          tgtGenName <- mapForGenName (obMode obl) srcGenName
          case M.lookup modeTgt (dGens tgtDoc) >>= M.lookup tgtGenName of
            Nothing ->
              Left
                ( "implements obligation "
                    <> obName obl
                    <> ": missing target generator "
                    <> renderModeName modeTgt
                    <> "."
                    <> renderGenName tgtGenName
                )
            Just gd ->
              if isTypeDeclGenNameInTables tgtDoc tgtCtorTables modeTgt (ObjName (renderGenName tgtGenName))
                then
                  Left
                    ( "implements obligation "
                        <> obName obl
                        <> ": target generator "
                        <> renderModeName modeTgt
                        <> "."
                        <> renderGenName tgtGenName
                        <> " is constructor-like"
                    )
                else Right [gd]
      where
        compSupportNames =
          case M.lookup modeTgt (mtClassifiedBy (dModes tgtDoc)) >>= cdComp of
            Just comp ->
              S.fromList [compCtxExt comp, compVar comp, compReindex comp]
            Nothing -> S.empty
        allModeGens =
          [ gd
          | gd <- M.elems (M.findWithDefault M.empty modeTgt (dGens tgtDoc))
          , not (isTypeDeclGenNameInTables tgtDoc tgtCtorTables modeTgt (ObjName (renderGenName (gdName gd))))
          , gdName gd `S.notMember` compSupportNames
          ]

    mapForGenName modeSrc srcGenName =
      case M.lookup (modeSrc, srcGenName) (morGenMap morph) of
        Nothing -> Right srcGenName
        Just image ->
          case singleGeneratorImageName (giDiagram image) of
            Just tgtGenName -> Right tgtGenName
            Nothing ->
              Left
                ( "implements obligation: source generator "
                    <> renderModeName modeSrc
                    <> "."
                    <> renderGenName srcGenName
                    <> " maps to a non-singleton generator image"
                )

    singleGeneratorImageName diag =
      case IM.elems (dEdges diag) of
        [edge] ->
          case ePayload edge of
            PGen g _ _ 
              | eIns edge == dIn diag
              , eOuts edge == dOut diag ->
                  Just g
            _ -> Nothing
        _ -> Nothing

    checkGeneratedSlot tt slotsByGen modeTgt gen obl label lhs rhs =
      case generatedSlotFor slotsByGen modeTgt gen obl of
        Nothing -> Right Nothing
        Just slot -> do
          case slotKind slot of
            SlotCtorTmArg -> do
              let lhsTmE = extractCtorSlotTerm gen slot lhs
              let rhsTmE = extractCtorSlotTerm gen slot rhs
              case (lhsTmE, rhsTmE) of
                (Right lhsTm, Right rhsTm) ->
                  case slotSig slot of
                    SlotTermSig _ sortTy -> do
                      let lhsCtx = dTmCtx (unTerm lhsTm)
                      let rhsCtx = dTmCtx (unTerm rhsTm)
                      case chooseHostTmCtx lhsCtx rhsCtx of
                        Nothing ->
                          Right Nothing
                        Just hostCtx -> do
                          ok <- defEqTermDiagram tt hostCtx sortTy lhsTm rhsTm
                          if ok
                            -- Slot-local ctor obligations are discharged on the designated term slot,
                            -- not by a whole-diagram join witness.
                            then Right (Just (ImplementsCheckProved [(label, ImplementsProofDefEq)]))
                            else Right Nothing
                    SlotBinderSig _ ->
                      Right Nothing
                _ ->
                  Right Nothing
            SlotBinder -> do
              let lhsArgE = extractBinderSlotArg gen slot lhs
              let rhsArgE = extractBinderSlotArg gen slot rhs
              case (lhsArgE, rhsArgE) of
                (Right lhsArg, Right rhsArg) -> do
                  ok <- defEqBinderArg tt lhsArg rhsArg
                  if ok
                    -- Slot-local binder obligations are discharged on the designated binder slot.
                    then Right (Just (ImplementsCheckProved [(label, ImplementsProofDefEq)]))
                    else Right Nothing
                _ ->
                  Right Nothing

    chooseHostTmCtx lhsCtx rhsCtx
      | lhsCtx == rhsCtx = Just lhsCtx
      | lhsCtx `L.isPrefixOf` rhsCtx = Just rhsCtx
      | rhsCtx `L.isPrefixOf` lhsCtx = Just lhsCtx
      | otherwise = Nothing

    generatedSlotFor slotsByGen modeTgt gen obl = do
      slots <- M.lookup (modeTgt, gdName gen) slotsByGen
      key <- generatedSlotKey (obName obl)
      law <- generatedLawSuffix (obName obl)
      let matches =
            [ s
            | s <- slots
            , sanitizeGeneratedSlotPath (sidPath (slotId s)) == key
            , generatedSlotLawAllowed obl law gen s
            ]
      case matches of
        [slot] -> Just slot
        _ -> Nothing

    generatedSlotLawAllowed obl law gen slot =
      if obGenerated obl && obForGen obl
        then
          case (slotKind slot, law) of
            (SlotCtorTmArg, "id_dom") -> True
            (SlotCtorTmArg, "id_cod") -> True
            (SlotCtorTmArg, "comp_dom") -> True
            (SlotCtorTmArg, "comp_cod") -> True
            (SlotBinder, "id_dom") -> True
            (SlotBinder, "id_cod") -> True
            (SlotBinder, "comp_dom") -> True
            (SlotBinder, "comp_cod") -> True
            (SlotBinder, "nat") -> True
            _ -> False
        else False

    generatedLawSuffix name =
      case reverse (T.splitOn "/" name) of
        law : _ -> Just law
        _ -> Nothing

    generatedSlotKey name =
      case T.splitOn "/" name of
        (_prefix : _mode : _gen : slotKey : _law : []) -> Just slotKey
        _ -> Nothing

    sanitizeGeneratedSlotPath =
      T.map (\c -> if isAlphaNum c || c == '/' || c == '_' || c == '-' then c else '_')

    extractBinderSlotArg gen slot diag = do
      (domIdx, pathTail) <- parseBinderSlotPath (sidPath (slotId slot))
      if null pathTail
        then Right ()
        else Left "generated slot obligation: unsupported binder slot path"
      binderIdx <- binderArgIndexForDomSlot gen domIdx
      bargs <- uniqueGenBinderArgs (gdName gen) diag
      nth "binder argument" binderIdx bargs

    parseBinderSlotPath path =
      case T.splitOn "." path of
        [] ->
          Left "generated slot obligation: empty slot path"
        root : rest ->
          case parseIndexed "dom[" root of
            Just domIdx -> Right (domIdx, rest)
            Nothing -> Left "generated slot obligation: binder slot root must be dom[...]"

    binderArgIndexForDomSlot gen domIdx =
      if domIdx < 0 || domIdx >= length (gdDom gen)
        then Left "generated slot obligation: binder slot domain index out of bounds"
        else
          let before = take domIdx (gdDom gen)
           in case gdDom gen !! domIdx of
                InBinder _ ->
                  Right (length [() | InBinder _ <- before])
                InPort _ ->
                  Left "generated slot obligation: slot path points to non-binder domain input"

    uniqueGenBinderArgs g diag =
      case
        [ bargs
        | edge <- IM.elems (dEdges diag)
        , PGen g' _ bargs <- [ePayload edge]
        , g' == g
        ]
      of
        [bargs] -> Right bargs
        [] -> Left "generated slot obligation: generator edge not found while extracting binder slot"
        _ -> Left "generated slot obligation: multiple generator edges found while extracting binder slot"

    defEqBinderArg tt lhsArg rhsArg =
      case (lhsArg, rhsArg) of
        (BAMeta l, BAMeta r) ->
          Right (l == r)
        (BAConcrete lhsDiag0, BAConcrete rhsDiag0) ->
          case chooseHostTmCtx (dTmCtx lhsDiag0) (dTmCtx rhsDiag0) of
            Nothing ->
              Right False
            Just hostCtx -> do
              lhsDiag <- weakenDiagramTmCtxTo hostCtx lhsDiag0
              rhsDiag <- weakenDiagramTmCtxTo hostCtx rhsDiag0
              lhsSeed <- normalizeForGeneratedObligation tt [] lhsDiag
              rhsSeed <- normalizeForGeneratedObligation tt [] rhsDiag
              diagramIsoEq lhsSeed rhsSeed
        _ ->
          Right False

    extractCtorSlotTerm gen slot diag = do
      let parts = T.splitOn "." (sidPath (slotId slot))
      case parts of
        [] ->
          Left "generated slot obligation: empty slot path"
        root : rest -> do
          (rootObj, tailSegs) <- extractRootObj gen root rest diag
          extractObjPath tailSegs rootObj

    extractRootObj gen seg rest diag
      | Just idx <- parseIndexed "dom[" seg =
          extractDomRootObj gen idx rest diag
      | Just idx <- parseIndexed "cod[" seg = do
          pid <- nth "codomain" idx (dOut diag)
          ty <- lookupPortTy "codomain" pid diag
          Right (ty, rest)
      | otherwise =
          Left "generated slot obligation: unsupported root slot path"

    extractDomRootObj gen domIdx rest diag =
      if domIdx < 0 || domIdx >= length (gdDom gen)
        then Left "generated slot obligation: domain index out of bounds"
        else
          case gdDom gen !! domIdx of
            InPort _ -> do
              let domPortIdx = length [() | InPort _ <- take domIdx (gdDom gen)]
              pid <- nth "domain" domPortIdx (dIn diag)
              ty <- lookupPortTy "domain" pid diag
              Right (ty, rest)
            InBinder _ -> do
              bdiag <- binderArgDiagramForDomSlot gen domIdx diag
              case rest of
                seg' : rest'
                  | Just idx <- parseIndexed "binderDom[" seg' -> do
                      pid <- nth "binder domain" idx (dIn bdiag)
                      ty <- lookupPortTy "binder domain" pid bdiag
                      Right (ty, rest')
                  | Just idx <- parseIndexed "binderCod[" seg' -> do
                      pid <- nth "binder codomain" idx (dOut bdiag)
                      ty <- lookupPortTy "binder codomain" pid bdiag
                      Right (ty, rest')
                  | Just idx <- parseIndexed "tmctx[" seg' -> do
                      ty <- nth "binder term context" idx (dTmCtx bdiag)
                      Right (ty, rest')
                _ ->
                  Left "generated slot obligation: binder ctor slot path must continue with binderDom/binderCod/tmctx"

    binderArgDiagramForDomSlot gen domIdx diag = do
      binderIdx <- binderArgIndexForDomSlot gen domIdx
      bargs <- uniqueGenBinderArgs (gdName gen) diag
      barg <- nth "binder argument" binderIdx bargs
      case barg of
        BAConcrete bdiag -> Right bdiag
        BAMeta _ -> Left "generated slot obligation: expected concrete binder argument for binder ctor slot path"

    extractObjPath segs obj =
      case segs of
        [] ->
          Left "generated slot obligation: slot path does not end at a term argument"
        seg : rest
          | seg == "mod" ->
              case objCode obj of
                CTMod me inner ->
                  extractObjPath rest (Obj { objOwnerMode = meSrc me, objCode = inner })
                _ ->
                  Left "generated slot obligation: expected modality wrapper in slot path"
          | Just idx <- parseIndexed "arg[" seg ->
              case objCode obj of
                CTCon _ args -> do
                  arg <- nth "constructor argument" idx args
                  case arg of
                    CATm tm ->
                      if null rest
                        then Right tm
                        else extractTermPath rest tm
                    CAObj ty ->
                      extractObjPath rest ty
                _ ->
                  Left "generated slot obligation: expected constructor in slot path"
          | otherwise ->
              Left "generated slot obligation: unsupported object slot segment"

    extractTermPath segs tm =
      case segs of
        "term" : rest -> stepTerm rest tm
        _ -> Left "generated slot obligation: expected term segment in slot path"
      where
        stepTerm [] term = Right term
        stepTerm (seg : rest) (TermDiagram termDiag)
          | Just idx <- parseIndexed "port[" seg = do
              ty <- nthIntMap "term port" idx (dPortObj termDiag)
              extractObjPath rest ty
          | Just idx <- parseIndexed "tmctx[" seg = do
              ty <- nth "term context" idx (dTmCtx termDiag)
              extractObjPath rest ty
          | Just idx <- parseIndexed "edge[" seg =
              case rest of
                "sort" : rest' -> do
                  edge <- nthIntMap "term edge" idx (dEdges termDiag)
                  case ePayload edge of
                    PTmMeta tv ->
                      extractObjPath rest' (tmvSort tv)
                    _ ->
                      Left "generated slot obligation: expected PTmMeta edge at term slot sort path"
                "box" : rest' -> do
                  edge <- nthIntMap "term edge" idx (dEdges termDiag)
                  case ePayload edge of
                    PBox _ inner ->
                      extractTermPath rest' (TermDiagram inner)
                    _ ->
                      Left "generated slot obligation: expected PBox edge at term slot box path"
                "feedback" : rest' -> do
                  edge <- nthIntMap "term edge" idx (dEdges termDiag)
                  case ePayload edge of
                    PFeedback inner ->
                      extractTermPath rest' (TermDiagram inner)
                    _ ->
                      Left "generated slot obligation: expected PFeedback edge at term slot feedback path"
                bargSeg : rest'
                  | Just bargIdx <- parseIndexed "barg[" bargSeg -> do
                      edge <- nthIntMap "term edge" idx (dEdges termDiag)
                      case ePayload edge of
                        PGen _ _ bargs -> do
                          barg <- nth "term binder argument" bargIdx bargs
                          case barg of
                            BAConcrete inner ->
                              extractTermPath rest' (TermDiagram inner)
                            BAMeta _ ->
                              Left "generated slot obligation: expected concrete term binder argument path"
                        _ ->
                          Left "generated slot obligation: expected PGen edge at term slot binder-arg path"
                _ ->
                  Left "generated slot obligation: expected .sort/.box/.feedback/.barg[...] after term edge segment"
          | otherwise =
              Left "generated slot obligation: unsupported term slot segment"

    parseIndexed prefix seg =
      if prefix `T.isPrefixOf` seg && "]" `T.isSuffixOf` seg
        then
          let inner = T.dropEnd 1 (T.drop (T.length prefix) seg)
           in case reads (T.unpack inner) of
                [(n, "")] -> Just n
                _ -> Nothing
        else Nothing

    nth label idx xs =
      if idx >= 0 && idx < length xs
        then Right (xs !! idx)
        else Left ("generated slot obligation: " <> label <> " index out of bounds")

    nthIntMap label idx table =
      case IM.lookup idx table of
        Just x -> Right x
        Nothing -> Left ("generated slot obligation: " <> label <> " index out of bounds")

    lookupPortTy label pid diag =
      case diagramPortObj diag pid of
        Just ty -> Right ty
        Nothing -> Left ("generated slot obligation: missing " <> label <> " port type")

    checkObligationJoin tt rules useGeneratedSeed label lhs rhs = do
      generatedOutcome <-
        if useGeneratedSeed
          then tryGeneratedSeed tt rules label lhs rhs
          else Right Nothing
      case generatedOutcome of
        Just out -> Right out
        Nothing -> runJoin tt rules label lhs rhs

    runJoin tt rules label lhs rhs = do
      proof <- autoJoinProof tt budget rules lhs rhs
      case proof of
        SearchUndecided lim ->
          Right (ImplementsCheckUndecided label lim)
        SearchProved witness -> do
          checkJoinProof tt rules witness
          Right (ImplementsCheckProved [(label, ImplementsProofJoin witness)])

    tryGeneratedSeed tt rules label lhs rhs = do
      lhsSeed <- normalizeForGeneratedObligation tt rules lhs
      rhsSeed <- normalizeForGeneratedObligation tt rules rhs
      same <- diagramIsoEq lhsSeed rhsSeed
      if same
        then do
          let witness =
                JoinProof
                  { jpLeft = RewritePath { rpStart = lhsSeed, rpSteps = [] }
                  , jpRight = RewritePath { rpStart = rhsSeed, rpSteps = [] }
                  }
          checkJoinProof tt rules witness
          Right (Just (ImplementsCheckProved [(label, ImplementsProofJoin witness)]))
        else do
          seedProof <- autoJoinProof tt budget rules lhsSeed rhsSeed
          case seedProof of
            SearchUndecided _ ->
              Right Nothing
            SearchProved witness -> do
              checkJoinProof tt rules witness
              Right (Just (ImplementsCheckProved [(label, ImplementsProofJoin witness)]))

    normalizeForGeneratedObligation tt _rules diag =
      case generatedCompRules of
        [] -> Right diag
        _ -> do
          status <- normalize tt generatedSeedFuel generatedCompRules diag
          pure $
            case status of
              Finished d -> d
              OutOfFuel d -> d

    generatedSeedFuel =
      let depthFuel = max 1 (sbMaxDepth budget * 4)
       in min 256 depthFuel

checkImplementsObligations :: ModuleEnv -> Doctrine -> Morphism -> Doctrine -> Either Text ()
checkImplementsObligations env tgtDoc morph ifaceDoc = do
  result <- checkImplementsObligationsWithBudget defaultSearchBudget env tgtDoc morph ifaceDoc
  case result of
    ImplementsCheckProved _ ->
      Right ()
    ImplementsCheckUndecided label lim ->
      Left
        ( "implements obligation undecided: "
            <> label
            <> " ("
            <> renderSearchLimit lim
            <> ")"
        )

mapObligationTyVar :: TypeTheory -> TypeTheory -> CtorTables -> Morphism -> TmVar -> Either Text TmVar
mapObligationTyVar ttSrc ttTgt tgtCtorTables morph v = do
  ownerSrc <- ownerModeForTypeMeta (morSrc morph) v
  ownerTgt <- applyMorphismMode morph ownerSrc
  sort' <- applyMorphismTyWithCaches ttSrc ttTgt tgtCtorTables morph (tmvSort v)
  pure v { tmvSort = sort', tmvOwnerMode = Just ownerTgt }

mapObligationTmVar :: TypeTheory -> TypeTheory -> CtorTables -> Morphism -> TmVar -> Either Text TmVar
mapObligationTmVar ttSrc ttTgt tgtCtorTables morph v = do
  sort' <- applyMorphismTyWithCaches ttSrc ttTgt tgtCtorTables morph (tmvSort v)
  pure v { tmvSort = sort', tmvOwnerMode = Nothing }

evalObligationExprMapped
  :: TypeTheory
  -> TypeTheory
  -> CtorTables
  -> ModuleEnv
  -> Doctrine
  -> Doctrine
  -> Morphism
  -> ModeName
  -> [TmVar]
  -> [TmVar]
  -> RawOblExpr
  -> Either Text Diagram
evalObligationExprMapped ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph mode tyVars tmVars expr = do
  modeTgt <- applyMorphismMode morph mode
  case expr of
    ROEDiag rawDiag -> do
      diagSrc <- elabObligationDiag env ifaceDoc mode [] tyVars tmVars rawDiag
      diagTgt <- applyMorphismDiagramWithTheories ttSrc ttTgt tgtCtorTables morph diagSrc
      if dMode diagTgt == modeTgt
        then Right diagTgt
        else Left "obligation: mapped diagram mode mismatch after morphism application"
    ROEMap rawMe innerExpr -> do
      me <- elabRawModExpr (dModes ifaceDoc) rawMe
      inner <- evalObligationExprMapped ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph (meSrc me) tyVars tmVars innerExpr
      meTgt <- applyMorphismModExpr morph me
      mapped <- applyModExpr tgtDoc meTgt inner
      if dMode mapped == modeTgt
        then Right mapped
        else Left "obligation map: mapped diagram mode does not match surrounding expression mode"
    ROEGen ->
      Left "obligation: @gen is only valid in for_gen obligations"
    ROELiftDom _ ->
      Left "obligation: lift_dom is only valid in for_gen obligations"
    ROELiftCod _ ->
      Left "obligation: lift_cod is only valid in for_gen obligations"
    ROEComp a b -> do
      d1 <- evalObligationExprMapped ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph mode tyVars tmVars a
      d2 <- evalObligationExprMapped ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph mode tyVars tmVars b
      compD ttTgt d2 d1
    ROETensor a b -> do
      d1 <- evalObligationExprMapped ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph mode tyVars tmVars a
      d2 <- evalObligationExprMapped ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph mode tyVars tmVars b
      tensorD d1 d2

data LiftBoundary
  = LiftOverDom
  | LiftOverCod
  deriving (Eq, Show)

evalObligationExprForGen
  :: TypeTheory
  -> TypeTheory
  -> CtorTables
  -> ModuleEnv
  -> Doctrine
  -> Doctrine
  -> Morphism
  -> ModeName
  -> [TmVar]
  -> [TmVar]
  -> Diagram
  -> RawOblExpr
  -> Either Text Diagram
evalObligationExprForGen ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph mode tyVars tmVars genDiag expr = do
  modeTgt <- applyMorphismMode morph mode
  case expr of
    ROEDiag rawDiag -> do
      diagSrc <- elabObligationDiag env ifaceDoc mode (dTmCtx genDiag) tyVars tmVars rawDiag
      diagTgt0 <- applyMorphismDiagramWithTheories ttSrc ttTgt tgtCtorTables morph diagSrc
      diagTgt <- weakenDiagramTmCtxTo (dTmCtx genDiag) diagTgt0
      if dMode diagTgt == modeTgt
        then Right diagTgt
        else Left "obligation: mapped diagram mode mismatch after morphism application"
    ROEMap rawMe innerExpr -> do
      me <- elabRawModExpr (dModes ifaceDoc) rawMe
      inner <- evalObligationExprForGen ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph (meSrc me) tyVars tmVars genDiag innerExpr
      meTgt <- applyMorphismModExpr morph me
      mapped <- applyModExpr tgtDoc meTgt inner
      if dMode mapped == modeTgt
        then Right mapped
        else Left "obligation map: mapped diagram mode does not match surrounding expression mode"
    ROEGen ->
      if dMode genDiag == modeTgt
        then Right genDiag
        else Left "obligation: @gen mode mismatch"
    ROELiftDom rawOp ->
      evalLiftedForGen ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph mode modeTgt tyVars tmVars genDiag LiftOverDom rawOp
    ROELiftCod rawOp ->
      evalLiftedForGen ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph mode modeTgt tyVars tmVars genDiag LiftOverCod rawOp
    ROEComp a b -> do
      d1 <- evalObligationExprForGen ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph mode tyVars tmVars genDiag a
      d2 <- evalObligationExprForGen ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph mode tyVars tmVars genDiag b
      compD ttTgt d2 d1
    ROETensor a b -> do
      d1 <- evalObligationExprForGen ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph mode tyVars tmVars genDiag a
      d2 <- evalObligationExprForGen ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph mode tyVars tmVars genDiag b
      tensorD d1 d2

evalLiftedForGen
  :: TypeTheory
  -> TypeTheory
  -> CtorTables
  -> ModuleEnv
  -> Doctrine
  -> Doctrine
  -> Morphism
  -> ModeName
  -> ModeName
  -> [TmVar]
  -> [TmVar]
  -> Diagram
  -> LiftBoundary
  -> RawDiagExpr
  -> Either Text Diagram
evalLiftedForGen ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph modeSrc modeTgt tyVars tmVars genDiag liftSide rawOp = do
  let ttDoc = ttTgt
  ctx <- case liftSide of
    LiftOverDom -> diagramDom genDiag
    LiftOverCod -> diagramCod genDiag
  ops <- mapM (instantiateAt ttDoc (dTmCtx genDiag)) ctx
  case ops of
    [] -> Right (idDTm modeTgt (dTmCtx genDiag) [])
    (d0:rest) -> foldM tensorD d0 rest
  where
    rigidTy = S.fromList tyVars
    rigidTm = S.fromList tmVars
    sideLabel =
      case liftSide of
        LiftOverDom -> "lift_dom"
        LiftOverCod -> "lift_cod"

    instantiateAt ttDoc tmCtx argTy = do
      opSrc <- elabObligationDiag env ifaceDoc modeSrc tmCtx tyVars tmVars rawOp
      opTgt0 <- applyMorphismDiagramWithTheories ttSrc ttTgt tgtCtorTables morph opSrc
      opTgt <- weakenDiagramTmCtxTo (dTmCtx genDiag) opTgt0
      if dMode opTgt == modeTgt
        then Right ()
        else Left "obligation: mapped diagram mode mismatch after morphism application"
      dom0 <- diagramDom opTgt
      if length dom0 /= 1
        then Left (sideLabel <> ": operator must have exactly one input ([x] -> [...])")
        else do
          let flexTy = S.difference (freeObjVarsDiagram opTgt) rigidTy
          let flexTm = S.difference (freeTmVarsDiagram opTgt) rigidTm
          let flex = S.union flexTy flexTm
          sDom <- U.unifyCtx ttDoc (dTmCtx opTgt) flex dom0 [argTy]
          applySubstDiagram ttDoc sDom opTgt

elabObligationDiag
  :: ModuleEnv
  -> Doctrine
  -> ModeName
  -> [Obj]
  -> [TmVar]
  -> [TmVar]
  -> RawDiagExpr
  -> Either Text Diagram
elabObligationDiag env doc mode tmCtx tyVars tmVars rawDiag = do
  (diag, _) <- elabDiagExprWith env doc mode tmCtx tyVars tmVars M.empty BMNoMeta False rawDiag
  ensureAttrVarNameSortsDiagram (freeAttrVarsDiagram diag)
  ensureAcyclicMode doc mode diag
  pure diag

mkForGenDiag :: ModeName -> GenDecl -> Either Text Diagram
mkForGenDiag mode gen = do
  let dom = gdPlainDom gen
  let cod = gdCod gen
  let attrs = forGenAttrs (gdAttrs gen)
  let bargs = forGenBinderArgs (gdDom gen)
  let (ins, d0) = allocPorts dom (emptyDiagram mode [])
  let (outs, d1) = allocPorts cod d0
  d2 <- addEdgePayload (PGen (gdName gen) attrs bargs) ins outs d1
  let d3 = d2 { dIn = ins, dOut = outs }
  validateDiagram d3
  pure d3
  where
    forGenAttrs fields =
      M.fromList
        [ (fieldName, ATVar (AttrVar ("for_gen_" <> fieldName) fieldSort))
        | (fieldName, fieldSort) <- fields
        ]

    forGenBinderArgs domShapes =
      [ BAMeta (BinderMetaVar ("for_gen_b" <> T.pack (show i)))
      | (i, _) <- zip [0 :: Int ..] [ () | InBinder _ <- domShapes ]
      ]

    allocPorts [] diag = ([], diag)
    allocPorts (ty:rest) diag =
      let (pid, diag1) = freshPort ty diag
          (pids, diag2) = allocPorts rest diag1
       in (pid : pids, diag2)

renderGenName :: GenName -> Text
renderGenName (GenName n) = n

ensureMode :: Doctrine -> ModeName -> Either Text ()
ensureMode doc mode =
  if M.member mode (mtModes (dModes doc))
    then Right ()
    else Left "unknown mode"

renderModeName :: ModeName -> Text
renderModeName (ModeName name) = name

provisionalCtorSort :: Doctrine -> ModeName -> Obj
provisionalCtorSort doc mode =
  case modeUniverseObj (dModes doc) mode of
    Just u -> u
    Nothing ->
      case classifierUniverse of
        Just u -> u
        Nothing ->
          Obj
            { objOwnerMode = mode
            , objCode =
                CTCon
                  ObjRef
                    { orMode = mode
                    , orName = ObjName "__provisional_universe"
                    }
                  []
            }
  where
    classifierUniverse =
      case
        [ cdUniverse decl
        | decl <- M.elems (mtClassifiedBy (dModes doc))
        , cdClassifier decl == mode
        , not (isPendingUniverseObj (cdUniverse decl))
        ]
      of
        (u:_) -> Just u
        [] -> Nothing

pendingClassUniverse :: ModeName -> RawPolyObjExpr -> Obj
pendingClassUniverse classifier raw =
  case raw of
    RPTVar name ->
      Obj
        { objOwnerMode = classifier
        , objCode =
            CTCon
              ObjRef
                { orMode = classifier
                , orName = ObjName name
                }
              []
        }
    RPTCon ref []
      | qualifierOk ref ->
          Obj
            { objOwnerMode = classifier
            , objCode =
                CTCon
                  ObjRef
                    { orMode = classifier
                    , orName = ObjName (rtrName ref)
                    }
                  []
            }
    _ ->
      OVar
        ObjVar
          { ovName = "__pending_universe"
          , ovMode = classifier
          }
  where
    qualifierOk ref =
      case rtrMode ref of
        Nothing -> True
        Just q -> ModeName q == classifier

isPendingUniverseObj :: Obj -> Bool
isPendingUniverseObj obj =
  case objCode obj of
    CTMeta v -> tmvName v == "__pending_universe"
    _ -> False

ensureAttrSort :: Doctrine -> AttrSort -> Either Text ()
ensureAttrSort doc sortName =
  if M.member sortName (dAttrSorts doc)
    then Right ()
    else Left "unknown attribute sort"

resolveTyVarMode :: Doctrine -> ModeName -> RawTyVarDecl -> Either Text ModeName
resolveTyVarMode doc defaultMode decl = do
  let mode = maybe defaultMode ModeName (rtvMode decl)
  ensureMode doc mode
  pure mode

resolveTyVarDecl :: Doctrine -> ModeName -> RawTyVarDecl -> Either Text TmVar
resolveTyVarDecl doc defaultMode decl = do
  mode <- resolveTyVarMode doc defaultMode decl
  mkTypeMetaVar doc mode (rtvName decl)

mkTypeMetaVar :: Doctrine -> ModeName -> Text -> Either Text TmVar
mkTypeMetaVar doc ownerMode name = do
  universe <-
    case modeUniverseObj (dModes doc) ownerMode of
      Nothing ->
        Left
          ( "type variable `"
              <> name
              <> "`: mode "
              <> renderMode ownerMode
              <> " missing classifiedBy universe"
          )
      Just u ->
        Right u
  pure
    TmVar
      { tmvName = name
      -- Code metavariables are sorted in the classifier universe object itself.
      , tmvSort = universe
      , tmvScope = 0
      , tmvOwnerMode = Just ownerMode
      }
  where
    renderMode (ModeName n) = n

ownerModeForTypeMeta :: Doctrine -> TmVar -> Either Text ModeName
ownerModeForTypeMeta doc v =
  case tmvOwnerMode v of
    Just owner
      | M.member owner (mtModes (dModes doc)) ->
          Right owner
      | otherwise ->
          Left
            ( "type metavariable `"
                <> tmvName v
                <> "` has unknown owner mode `"
                <> renderMode owner
                <> "`"
            )
    Nothing ->
      Left
        ( "type metavariable `"
            <> tmvName v
            <> "` is missing an explicit owner mode"
        )
  where
    renderMode (ModeName n) = n

elabTmDeclVar :: Doctrine -> ModeName -> [TmVar] -> RawTmVarDecl -> Either Text TmVar
elabTmDeclVar doc defaultMode tyVars decl = do
  sortTy <-
    case elabObjExpr doc tyVars [] M.empty defaultMode (rtvdSort decl) of
      Right ty -> Right ty
      Left _ -> elabObjExprInferOwner doc tyVars [] M.empty (rtvdSort decl)
  pure TmVar { tmvName = rtvdName decl, tmvSort = sortTy, tmvScope = 0, tmvOwnerMode = Nothing }

elabParamDecls :: Doctrine -> ModeName -> [RawParamDecl] -> Either Text ([TmVar], [TmVar], [GenParam])
elabParamDecls doc defaultMode params = go 0 [] [] [] params
  where
    go _ tyAcc tmAcc paramAcc [] = Right (reverse tyAcc, reverse tmAcc, reverse paramAcc)
    go i tyAcc tmAcc paramAcc (p:rest) =
      case p of
        RPDType tvDecl -> do
          ownerMode <- resolveTyVarMode doc defaultMode tvDecl
          tv <- mkTypeMetaVar doc ownerMode (rtvName tvDecl)
          let name = ovName tv
          if name `elem` map ovName tyAcc || name `elem` map tmvName tmAcc
            then Left "duplicate parameter name"
            else go (i + 1) (tv:tyAcc) tmAcc (GP_Ty tv : paramAcc) rest
        RPDTerm tmDecl -> do
          let name = rtvdName tmDecl
          if name `elem` map ovName tyAcc || name `elem` map tmvName tmAcc
            then Left "duplicate parameter name"
            else do
              tmVar <- elabTmDeclVar doc defaultMode tyAcc tmDecl
              go (i + 1) tyAcc (tmVar:tmAcc) (GP_Tm tmVar : paramAcc) rest

buildTypeTemplateParams
  :: Doctrine
  -> M.Map ModeName ModeName
  -> [TypeParamSig]
  -> [RawParamDecl]
  -> Either Text ([TemplateParam], [TmVar], [TmVar])
buildTypeTemplateParams tgt modeMap sigParams decls = do
  if length sigParams /= length decls
    then Left "morphism: type mapping binder arity mismatch"
    else go [] [] [] (zip sigParams decls)
  where
    go tyAcc tmAcc tmplAcc [] =
      Right (reverse tmplAcc, reverse tyAcc, reverse tmAcc)
    go tyAcc tmAcc tmplAcc ((sigParam, decl):rest) =
      case (sigParam, decl) of
        (TPS_Ty srcMode, RPDType tyDecl) -> do
          expectedMode <- lookupMappedMode srcMode
          tyVar <- resolveTyVarDecl tgt expectedMode tyDecl
          ensureFreshName tyAcc tmAcc (ovName tyVar)
          go (tyVar:tyAcc) tmAcc (TPType tyVar:tmplAcc) rest
        (TPS_Tm srcSort, RPDTerm tmDecl) -> do
          expectedMode <- lookupMappedMode (objOwnerMode srcSort)
          tmSort <- elabObjExpr tgt (reverse tyAcc) (reverse tmAcc) M.empty expectedMode (rtvdSort tmDecl)
          if objOwnerMode tmSort /= expectedMode
            then Left "morphism: type mapping term binder mode mismatch"
            else Right ()
          ensureFreshName tyAcc tmAcc (rtvdName tmDecl)
          let tmVar = TmVar { tmvName = rtvdName tmDecl, tmvSort = tmSort, tmvScope = 0, tmvOwnerMode = Nothing }
          go tyAcc (tmVar:tmAcc) (TPTm tmVar:tmplAcc) rest
        (TPS_Ty _, _) ->
          Left "morphism: type mapping binder kind mismatch"
        (TPS_Tm _, _) ->
          Left "morphism: type mapping binder kind mismatch"

    ensureFreshName tyAcc tmAcc name =
      let tyNames = map ovName tyAcc
          tmNames = map tmvName tmAcc
      in if name `elem` tyNames || name `elem` tmNames
          then Left "morphism: duplicate type mapping binders"
          else Right ()

    lookupMappedMode srcMode =
      case M.lookup srcMode modeMap of
        Nothing -> Left "morphism: missing mode mapping"
        Just tgtMode -> Right tgtMode

elabContext :: Doctrine -> ModeName -> [TmVar] -> [TmVar] -> M.Map Text (Int, Obj) -> RawPolyContext -> Either Text Context
elabContext doc expectedMode tyVars tmVars tmBound ctx = do
  ctorTables <- deriveCtorTablesForElab doc
  elabContextWithTables doc ctorTables expectedMode tyVars tmVars tmBound ctx

elabContextWithTables
  :: Doctrine
  -> CtorTables
  -> ModeName
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> RawPolyContext
  -> Either Text Context
elabContextWithTables doc ctorTables expectedMode tyVars tmVars tmBound ctx = do
  tys <- mapM (elabObjExprWithTables doc ctorTables tyVars tmVars tmBound expectedMode) ctx
  let bad = filter (\ty -> objOwnerMode ty /= expectedMode) tys
  if null bad
    then Right tys
    else Left "boundary type must match generator mode"

elabObjExpr
  :: Doctrine
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> ModeName
  -> RawPolyObjExpr
  -> Either Text Obj
elabObjExpr doc tyVars tmVars tmBound expectedOwnerMode expr = do
  ctorTables <- deriveCtorTablesForElab doc
  elabObjExprWithTables doc ctorTables tyVars tmVars tmBound expectedOwnerMode expr

elabObjExprWithTables
  :: Doctrine
  -> CtorTables
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> ModeName
  -> RawPolyObjExpr
  -> Either Text Obj
elabObjExprWithTables doc ctorTables tyVars tmVars tmBound expectedOwnerMode expr =
  case expr of
    RPTVar name -> do
      case [v | v <- tyVars, ovName v == name] of
        [v] -> do
          ownerMode <- ownerModeForTypeMeta doc v
          if ownerMode == expectedOwnerMode
            then Right Obj { objOwnerMode = expectedOwnerMode, objCode = CTMeta v }
            else Left "type variable mode mismatch"
        (_:_:_) -> Left ("duplicate type variable name: " <> name)
        [] -> do
          ref <-
            resolveTypeRefInClassifierInTables
              doc
              ctorTables
              expectedOwnerMode
              classifierMode
              RawTypeRef
                { rtrMode = Nothing
                , rtrName = name
                }
          params <- lookupCtorSigForOwnerInTables doc ctorTables expectedOwnerMode ref
          if null params
            then Right Obj { objOwnerMode = expectedOwnerMode, objCode = CTCon ref [] }
            else Left "type constructor arity mismatch"
    RPTMod rawMe innerRaw -> do
      me <- elabRawModExpr (dModes doc) rawMe
      if meTgt me == expectedOwnerMode
        then Right ()
        else Left "modality application target/object mode mismatch"
      inner <- elabObjExprWithTables doc ctorTables tyVars tmVars tmBound (meSrc me) innerRaw
      if objOwnerMode inner /= meSrc me
        then Left "modality application source/argument mode mismatch"
        else
          normalizeObjExpr
            (dModes doc)
            Obj
              { objOwnerMode = expectedOwnerMode
              , objCode = CTMod me (objCode inner)
              }
    RPTCon rawRef args -> do
      case asModalityCall rawRef args of
        Just (rawMe, innerRaw) -> do
          me <- elabRawModExpr (dModes doc) rawMe
          if meTgt me == expectedOwnerMode
            then Right ()
            else Left "modality application target/object mode mismatch"
          inner <- elabObjExprWithTables doc ctorTables tyVars tmVars tmBound (meSrc me) innerRaw
          if objOwnerMode inner /= meSrc me
            then Left "modality application source/argument mode mismatch"
            else
              normalizeObjExpr
                (dModes doc)
                Obj
                  { objOwnerMode = expectedOwnerMode
                  , objCode = CTMod me (objCode inner)
                  }
        Nothing -> do
          ref <- resolveTypeRefInClassifierInTables doc ctorTables expectedOwnerMode classifierMode rawRef
          params <- lookupCtorSigForOwnerInTables doc ctorTables expectedOwnerMode ref
          if length params /= length args
            then Left "type constructor arity mismatch"
            else do
              args' <- mapM (elabOneArg params) (zip params args)
              Right Obj { objOwnerMode = expectedOwnerMode, objCode = CTCon ref args' }
  where
    classifierMode = modeClassifierMode (dModes doc) expectedOwnerMode

    elabOneArg _ (TPS_Ty m, rawArg) = do
      argTy <- elabObjExprWithTables doc ctorTables tyVars tmVars tmBound m rawArg
      if objOwnerMode argTy == m
        then Right (CAObj argTy)
        else Left "type constructor argument mode mismatch"
    elabOneArg _ (TPS_Tm sortTy, rawArg) = do
      tmArg <- elabTmTermWithTables doc ctorTables tyVars tmVars tmBound (Just sortTy) rawArg
      Right (CATm tmArg)

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
      case
        resolveTypeRefInClassifierMaybeInTables
          doc
          ctorTables
          expectedOwnerMode
          classifierMode
          RawTypeRef
            { rtrMode = Just modeTok
            , rtrName = tyTok
            }
      of
        Right (Just _) -> True
        _ -> False

elabObjExprInferOwner
  :: Doctrine
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> RawPolyObjExpr
  -> Either Text Obj
elabObjExprInferOwner doc tyVars tmVars tmBound expr = do
  ctorTables <- deriveCtorTablesForElab doc
  elabObjExprInferOwnerWithTables doc ctorTables tyVars tmVars tmBound expr

elabObjExprInferOwnerWithTables
  :: Doctrine
  -> CtorTables
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> RawPolyObjExpr
  -> Either Text Obj
elabObjExprInferOwnerWithTables doc ctorTables tyVars tmVars tmBound expr =
  case successes of
    [(_, obj)] -> Right obj
    [] ->
      case failures of
        (err:_) -> Left err
        [] -> Left "unable to infer object mode"
    _ ->
      Left "ambiguous object expression mode (qualify constructors or use a variable with explicit mode)"
  where
    modes = M.keys (mtModes (dModes doc))
    attempts = [ (m, elabObjExprWithTables doc ctorTables tyVars tmVars tmBound m expr) | m <- modes ]
    successes = [ (m, obj) | (m, Right obj) <- attempts ]
    failures = [ err | (_, Left err) <- attempts ]

elabTmTerm
  :: Doctrine
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> Maybe Obj
  -> RawPolyObjExpr
  -> Either Text TermDiagram
elabTmTerm doc tyVars tmVars tmBound mExpected raw = do
  ctorTables <- deriveCtorTablesForElab doc
  elabTmTermWithTables doc ctorTables tyVars tmVars tmBound mExpected raw

elabTmTermWithTables
  :: Doctrine
  -> CtorTables
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> Maybe Obj
  -> RawPolyObjExpr
  -> Either Text TermDiagram
elabTmTermWithTables doc ctorTables _tyVars tmVars tmBound mExpected raw =
  do
    ttDoc <- doctrineTypeTheoryFromTables doc ctorTables
    (expr, inferredSort) <- elabExpr ctorTables mExpected raw
    let expectedSort = maybe inferredSort id mExpected
    tmCtx <- mkTmCtx
    termExprToDiagramChecked ttDoc tmCtx expectedSort expr
  where
    elabExpr ctorTables mExp tmRaw =
      case tmRaw of
        RPTMod _ _ -> Left "term arguments do not support modality application"
        RPTVar name ->
          case M.lookup name tmBound of
            Just (idx, sortTy) -> Right (TMBound idx, sortTy)
            Nothing ->
              case [v | v <- tmVars, tmvName v == name] of
                [v] -> Right (TMVar v, tmvSort v)
                (_:_:_) -> Left ("duplicate term variable name: " <> name)
                [] ->
                  case mExp of
                    Nothing -> do
                      (funName, sig) <- lookupTmFunAnyInTables doc ctorTables name 0
                      pure (TMFun funName [], tfsRes sig)
                    Just expected -> do
                      (funName, sig) <- lookupTmFunByNameInTables doc ctorTables expected name 0
                      pure (TMFun funName [], tfsRes sig)
        RPTCon rawRef args ->
          case rtrMode rawRef of
            Just _ -> Left "term function names must be unqualified"
            Nothing -> do
              (funName, sig) <-
                case mExp of
                  Just expected -> lookupTmFunByNameInTables doc ctorTables expected (rtrName rawRef) (length args)
                  Nothing -> lookupTmFunAnyInTables doc ctorTables (rtrName rawRef) (length args)
              argExprs <- mapM (\(argSort, argRaw) -> fst <$> elabExpr ctorTables (Just argSort) argRaw) (zip (tfsArgs sig) args)
              pure (TMFun funName argExprs, tfsRes sig)

    mkTmCtx =
      if M.null tmBound
        then Right []
        else do
          let idxMap = M.fromList [ (idx, ty) | (idx, ty) <- M.elems tmBound ]
          let maxIdx = maximum (M.keys idxMap)
          mapM
            (\i ->
              case M.lookup i idxMap of
                Just ty -> Right ty
                Nothing -> Left "term argument uses sparse bound term context")
            [0 .. maxIdx]

lookupTmFunByNameInTables :: Doctrine -> CtorTables -> Obj -> Text -> Int -> Either Text (TmFunName, TmFunSig)
lookupTmFunByNameInTables doc ctorTables expectedSort name arity =
  let fname = TmFunName name
      sigs = gatherCandidates ctorTables (objOwnerMode expectedSort)
   in case sigs of
        [] -> Left ("unknown term function: " <> name)
        [sig] ->
          if length (tfsArgs sig) == arity
            then Right (fname, sig)
            else Left "term function arity mismatch"
        _ -> Left ("ambiguous term function in mode: " <> name)
  where
    gatherCandidates ctorTables' mode =
      let fromGens =
            [ TmFunSig
                { tfsArgs = [ ty | InPort ty <- gdDom gd ]
                , tfsRes = res
                }
            | gd <- maybe [] M.elems (M.lookup mode (dGens doc))
            , gdName gd == GenName name
            , not (isTypeDeclGenNameInTables doc ctorTables' mode (ObjName (renderGenName (gdName gd))))
            , null (gdTyVars gd)
            , null (gdTmVars gd)
            , null (gdAttrs gd)
            , all isPort (gdDom gd)
            , [res] <- [gdCod gd]
            ]
       in fromGens
    isPort sh =
      case sh of
        InPort _ -> True
        InBinder _ -> False

lookupTmFunAnyInTables :: Doctrine -> CtorTables -> Text -> Int -> Either Text (TmFunName, TmFunSig)
lookupTmFunAnyInTables doc ctorTables name arity =
  case genCandidates ctorTables of
    [] -> Left ("unknown term function: " <> name)
    [single] -> Right single
    _ -> Left ("ambiguous term function: " <> name)
  where
    genCandidates ctorTables' =
      [ ( TmFunName name
        , TmFunSig
            { tfsArgs = [ ty | InPort ty <- gdDom gd ]
            , tfsRes = res
            }
        )
      | modeTable <- M.elems (dGens doc)
      , gd <- M.elems modeTable
      , not (isTypeDeclGenNameInTables doc ctorTables' (gdMode gd) (ObjName (renderGenName (gdName gd))))
      , gdName gd == GenName name
      , null (gdTyVars gd)
      , null (gdTmVars gd)
      , null (gdAttrs gd)
      , all isPort (gdDom gd)
      , [res] <- [gdCod gd]
      , length [ ty | InPort ty <- gdDom gd ] == arity
      ]
    isPort sh =
      case sh of
        InPort _ -> True
        InBinder _ -> False

elabInputShapes :: Doctrine -> ModeName -> [TmVar] -> [TmVar] -> [RawInputShape] -> Either Text [InputShape]
elabInputShapes doc mode tyVars tmVars shapes = do
  ctorTables <- deriveCtorTablesForElab doc
  mapM (elabInputShapeWithTables doc ctorTables mode tyVars tmVars) shapes

elabInputShapeWithTables
  :: Doctrine
  -> CtorTables
  -> ModeName
  -> [TmVar]
  -> [TmVar]
  -> RawInputShape
  -> Either Text InputShape
elabInputShapeWithTables doc ctorTables mode tyVars tmVars shape =
  case shape of
    RIPort rawTy -> InPort <$> elabObjExprWithTables doc ctorTables tyVars tmVars M.empty mode rawTy
    RIBinder binders rawCod -> do
      boundTys <- mapM (\b -> elabObjExprInferOwnerWithTables doc ctorTables tyVars tmVars M.empty (rbvType b)) binders
      let binderPairs = zip binders boundTys
      let tmBinders = [ (rbvName b, ty) | (b, ty) <- binderPairs, objOwnerMode ty /= mode ]
      let termBinders = [ b | (b, ty) <- binderPairs, objOwnerMode ty == mode ]
      let tmCtx = map snd tmBinders
      let tmBound = M.fromList (zipWith (\(nm, ty) idx -> (nm, (idx, ty))) tmBinders [0..])
      bsDom <- mapM (\b -> elabObjExprWithTables doc ctorTables tyVars tmVars tmBound mode (rbvType b)) termBinders
      bsCod <- elabContextWithTables doc ctorTables mode tyVars tmVars tmBound rawCod
      pure (InBinder BinderSig { bsTmCtx = tmCtx, bsDom = bsDom, bsCod = bsCod })

data BinderMetaMode
  = BMNoMeta
  | BMCollect
  | BMUse
  deriving (Eq, Show)

elabRuleLHS
  :: ModuleEnv
  -> Doctrine
  -> ModeName
  -> [TmVar]
  -> [TmVar]
  -> RawDiagExpr
  -> Either Text (Diagram, M.Map BinderMetaVar BinderSig)
elabRuleLHS env doc mode tyVars tmVars expr = do
  (diag, metas) <- elabDiagExprWith env doc mode [] tyVars tmVars M.empty BMCollect False expr
  ensureAttrVarNameSortsDiagram (freeAttrVarsDiagram diag)
  ensureAcyclicMode doc mode diag
  pure (diag, metas)

elabRuleRHS
  :: ModuleEnv
  -> Doctrine
  -> ModeName
  -> [TmVar]
  -> [TmVar]
  -> M.Map BinderMetaVar BinderSig
  -> RawDiagExpr
  -> Either Text Diagram
elabRuleRHS env doc mode tyVars tmVars binderSigs expr = do
  (diag, metas) <- elabDiagExprWith env doc mode [] tyVars tmVars binderSigs BMUse True expr
  if metas == binderSigs
    then do
      ensureAttrVarNameSortsDiagram (freeAttrVarsDiagram diag)
      ensureAcyclicMode doc mode diag
      pure diag
    else Left "rule RHS introduces fresh binder metas"

elabDiagExpr :: ModuleEnv -> Doctrine -> ModeName -> [TmVar] -> RawDiagExpr -> Either Text Diagram
elabDiagExpr env doc mode ruleVars expr = do
  (diag, _) <- elabDiagExprWith env doc mode [] ruleVars [] M.empty BMNoMeta False expr
  ensureAttrVarNameSortsDiagram (freeAttrVarsDiagram diag)
  ensureAcyclicMode doc mode diag
  pure diag

elabDiagExprWith
  :: ModuleEnv
  -> Doctrine
  -> ModeName
  -> [Obj]
  -> [TmVar]
  -> [TmVar]
  -> M.Map BinderMetaVar BinderSig
  -> BinderMetaMode
  -> Bool
  -> RawDiagExpr
  -> Either Text (Diagram, M.Map BinderMetaVar BinderSig)
elabDiagExprWith env doc mode tmCtx tyVars tmVars binderSigs0 metaMode allowSplice expr =
  ensureLinearMetaVars expr *> evalFresh (elabDiagExprWithFresh env doc mode tmCtx tyVars tmVars binderSigs0 metaMode allowSplice expr)

elabDiagExprWithFresh
  :: ModuleEnv
  -> Doctrine
  -> ModeName
  -> [Obj]
  -> [TmVar]
  -> [TmVar]
  -> M.Map BinderMetaVar BinderSig
  -> BinderMetaMode
  -> Bool
  -> RawDiagExpr
  -> Fresh (Diagram, M.Map BinderMetaVar BinderSig)
elabDiagExprWithFresh env doc mode tmCtx tyVars tmVars binderSigs0 metaMode allowSplice expr = do
  ttDoc <- liftEither (doctrineTypeTheory doc)
  let ctorTables = ttCtorTables ttDoc
  build ttDoc ctorTables tmCtx binderSigs0 expr
  where
    rigidTy = S.fromList tyVars
    rigidTm = S.fromList tmVars

    elabOneParamArg ttDoc ctorTables curTmCtx tyFreshMap tmFreshMap (tyAcc, tmAcc) (paramKind, rawArg) =
      case paramKind of
        GP_Ty tyVar0 -> do
          freshTyVar <-
            case M.lookup tyVar0 tyFreshMap of
              Nothing -> liftEither (Left "internal error: missing fresh type parameter")
              Just v -> pure v
          ownerMode <- liftEither (ownerModeForTypeMeta doc freshTyVar)
          tyArg <- liftEither (elabObjExprWithTables doc ctorTables tyVars tmVars M.empty ownerMode rawArg)
          if objOwnerMode tyArg == ownerMode
            then pure ((freshTyVar, tyArg) : tyAcc, tmAcc)
            else liftEither (Left "generator type argument mode mismatch")
        GP_Tm tmVar0 -> do
          freshTmVar <-
            case M.lookup tmVar0 tmFreshMap of
              Nothing -> liftEither (Left "internal error: missing fresh term parameter")
              Just v -> pure v
          tmArg <- elabTmArg ttDoc curTmCtx freshTmVar rawArg
          pure (tyAcc, (freshTmVar, tmArg) : tmAcc)

    build ttDoc ctorTables curTmCtx binderSigs e =
      case e of
        RDId ctx -> do
          ctx' <- liftEither (elabContextWithTables doc ctorTables mode tyVars tmVars M.empty ctx)
          pure (idDTm mode curTmCtx ctx', binderSigs)
        RDMetaVar name -> do
          (_, ty) <- freshTyVar doc ObjVar { ovName = "mv_" <> name, ovMode = mode }
          let (pid, d0) = freshPort ty (emptyDiagram mode curTmCtx)
          d1 <- liftEither (setPortLabel pid name d0)
          pure (d1 { dIn = [pid], dOut = [pid] }, binderSigs)
        RDGen name mArgs mAttrArgs mBinderArgs -> do
          gen <- liftEither (lookupGen doc mode (GenName name))
          tyRename <- freshTySubst doc (gdTyVars gen)
          tmRename <- freshTmSubst ttDoc curTmCtx (gdTmVars gen)
          let renameSubst = U.mkSubst tyRename tmRename
          dom0 <- applySubstCtxDoc ttDoc renameSubst (gdPlainDom gen)
          cod0 <- applySubstCtxDoc ttDoc renameSubst (gdCod gen)
          binderSlots0 <- mapM (applySubstBinderSig ttDoc renameSubst) [ bs | InBinder bs <- gdDom gen ]
          (dom, cod, binderSlots) <-
            case mArgs of
              Nothing -> pure (dom0, cod0, binderSlots0)
              Just args -> do
                let paramOrder = gdParams gen
                if length args /= length paramOrder
                  then liftEither (Left "generator type/term argument mismatch")
                  else do
                    freshTyVars <- liftEither (extractFreshTyVars (gdTyVars gen) tyRename)
                    freshTmVars <- liftEither (extractFreshTmVars (gdTmVars gen) tmRename)
                    let tyFreshMap = M.fromList (zip (gdTyVars gen) freshTyVars)
                    let tmFreshMap = M.fromList (zip (gdTmVars gen) freshTmVars)
                    (tyBinds, tmBinds) <-
                      foldM
                        (elabOneParamArg ttDoc ctorTables curTmCtx tyFreshMap tmFreshMap)
                        ([], [])
                        (zip paramOrder args)
                    let argSubst =
                          U.mkSubst
                            (M.fromList (reverse tyBinds))
                            (M.fromList (reverse tmBinds))
                    dom1 <- applySubstCtxDoc ttDoc argSubst dom0
                    cod1 <- applySubstCtxDoc ttDoc argSubst cod0
                    binderSlots1 <- mapM (applySubstBinderSig ttDoc argSubst) binderSlots0
                    pure (dom1, cod1, binderSlots1)
          attrs <- liftEither (elabGenAttrs doc gen mAttrArgs)
          (binderArgs, binderSigs') <- elaborateBinderArgs ttDoc binderSigs binderSlots mBinderArgs
          diag <- liftEither (mkGenDiag curTmCtx (gdName gen) attrs binderArgs dom cod)
          pure (diag, binderSigs')
        RDTermRef name -> do
          term <- liftEither (lookupTerm env name)
          if tdDoctrine term == dName doc
            then
              if tdMode term /= mode
                then liftEither (Left ("term @" <> name <> " has mode " <> renderModeName (tdMode term) <> ", expected " <> renderModeName mode))
                else
                  if dTmCtx (tdDiagram term) == curTmCtx
                    then pure (tdDiagram term, binderSigs)
                    else liftEither (Left ("term @" <> name <> " has incompatible term context"))
            else do
              srcDoc <- liftEither (lookupDoctrine env (tdDoctrine term))
              (doc', diag') <- liftEither (coerceDiagramTo env srcDoc (tdDiagram term) (dName doc))
              if dName doc' /= dName doc
                then liftEither (Left ("term @" <> name <> " has doctrine " <> tdDoctrine term <> ", expected " <> dName doc))
                else if dMode diag' /= mode
                  then liftEither (Left ("term @" <> name <> " has mode " <> renderModeName (dMode diag') <> ", expected " <> renderModeName mode))
                  else
                    if dTmCtx diag' == curTmCtx
                      then pure (diag', binderSigs)
                      else liftEither (Left ("term @" <> name <> " has incompatible term context"))
        RDSplice name ->
          if allowSplice
            then do
              let meta = BinderMetaVar name
              sig <- liftEither $
                case M.lookup meta binderSigs of
                  Nothing -> Left "splice references unknown binder meta"
                  Just bs -> Right bs
              diag <- liftEither (mkSpliceDiag curTmCtx meta (bsDom sig) (bsCod sig))
              pure (diag, binderSigs)
            else liftEither (Left "splice is only allowed in rule RHS")
        RDBox name innerExpr -> do
          (inner, binderSigs') <- build ttDoc ctorTables curTmCtx binderSigs innerExpr
          dom <- liftEither (diagramDom inner)
          cod <- liftEither (diagramCod inner)
          let (ins, diag0) = allocPorts dom (emptyDiagram mode curTmCtx)
          let (outs, diag1) = allocPorts cod diag0
          diag2 <- liftEither (addEdgePayload (PBox (BoxName name) inner) ins outs diag1)
          let diag3 = diag2 { dIn = ins, dOut = outs }
          liftEither (validateDiagram diag3)
          pure (diag3, binderSigs')
        RDLoop innerExpr -> do
          (inner, binderSigs') <- build ttDoc ctorTables curTmCtx binderSigs innerExpr
          case (dIn inner, dOut inner) of
            ([pIn], pState:pOuts) -> do
              stateInTy <- liftEither (lookupPortTy inner pIn)
              stateOutTy <- liftEither (lookupPortTy inner pState)
              if stateInTy == stateOutTy
                then pure ()
                else liftEither (Left "loop: body first output type must match input type")
              outTys <- mapM (liftEither . lookupPortTy inner) pOuts
              let (outs, diag0) = allocPorts outTys (emptyDiagram mode curTmCtx)
              diag1 <- liftEither (addEdgePayload (PFeedback inner) [] outs diag0)
              let diag2 = diag1 { dIn = [], dOut = outs }
              liftEither (validateDiagram diag2)
              pure (diag2, binderSigs')
            _ -> liftEither (Left "loop: expected exactly one input and at least one output")
        RDMap rawMe innerExpr -> do
          me <- liftEither (elabRawModExpr (dModes doc) rawMe)
          (inner, binderSigs') <-
            elabDiagExprWithFresh
              env
              doc
              (meSrc me)
              curTmCtx
              tyVars
              tmVars
              binderSigs
              metaMode
              allowSplice
              innerExpr
          mapped <- liftEither (applyModExpr doc me inner)
          if dMode mapped == mode
            then pure (mapped, binderSigs')
            else liftEither (Left "map: mapped diagram mode does not match surrounding expression mode")
        RDComp a b -> do
          (d1, binderSigs1) <- build ttDoc ctorTables curTmCtx binderSigs a
          (d2, binderSigs2) <- build ttDoc ctorTables curTmCtx binderSigs1 b
          dComp <- liftEither (compD ttDoc d2 d1)
          pure (dComp, binderSigs2)
        RDTensor a b -> do
          (d1, binderSigs1) <- build ttDoc ctorTables curTmCtx binderSigs a
          (d2, binderSigs2) <- build ttDoc ctorTables curTmCtx binderSigs1 b
          dTen <- liftEither (tensorD d1 d2)
          pure (dTen, binderSigs2)

    elaborateBinderArgs ttDoc binderSigs binderSlots mBinderArgs =
      case (binderSlots, mBinderArgs) of
        ([], Nothing) -> pure ([], binderSigs)
        ([], Just []) -> pure ([], binderSigs)
        ([], Just _) -> liftEither (Left "generator does not accept binder arguments")
        (_:_, Nothing) -> liftEither (Left "missing generator binder arguments")
        (_, Just rawArgs) ->
          if length binderSlots /= length rawArgs
            then liftEither (Left "generator binder argument mismatch")
            else foldM step ([], binderSigs) (zip binderSlots rawArgs)
      where
        step (acc, bsMap) (slot, rawArg) =
          case rawArg of
            RBAExpr exprArg -> do
              (diagArg, _) <-
                elabDiagExprWithFresh
                  env
                  doc
                  mode
                  (bsTmCtx slot)
                  tyVars
                  tmVars
                  M.empty
                  BMNoMeta
                  False
                  exprArg
              diagArg' <- liftEither (unifyBoundary ttDoc rigidTy rigidTm (bsDom slot) (bsCod slot) diagArg)
              domArg <- liftEither (diagramDom diagArg')
              codArg <- liftEither (diagramCod diagArg')
              domArg' <- canonicalCtx ttDoc domArg
              codArg' <- canonicalCtx ttDoc codArg
              slotDom' <- canonicalCtx ttDoc (bsDom slot)
              slotCod' <- canonicalCtx ttDoc (bsCod slot)
              if domArg' == slotDom' && codArg' == slotCod'
                then pure (acc <> [BAConcrete diagArg'], bsMap)
                else liftEither (Left "binder argument boundary mismatch")
            RBAMeta name ->
              case metaMode of
                BMNoMeta ->
                  liftEither (Left "binder metavariables are only allowed in rule diagrams")
                BMCollect -> do
                  let key = BinderMetaVar name
                  case M.lookup key bsMap of
                    Nothing -> pure (acc <> [BAMeta key], M.insert key slot bsMap)
                    Just slot'
                      | slot' == slot -> pure (acc <> [BAMeta key], bsMap)
                      | otherwise -> liftEither (Left "binder meta reused with inconsistent signature")
                BMUse -> do
                  let key = BinderMetaVar name
                  case M.lookup key bsMap of
                    Nothing -> liftEither (Left "RHS introduces unknown binder meta")
                    Just slot'
                      | slot' == slot -> pure (acc <> [BAMeta key], bsMap)
                      | otherwise -> liftEither (Left "binder meta used with inconsistent signature")

    elabTmArg ttDoc curTmCtx v rawArg =
      case elabTmTerm doc tyVars tmVars M.empty (Just (tmvSort v)) rawArg of
        Right tm -> pure tm
        Left err ->
          case rawArg of
            RPTVar name ->
              case implicitBoundCandidate curTmCtx (tmvSort v) of
                Right (Just idx) ->
                  case termExprToDiagramChecked ttDoc curTmCtx (tmvSort v) (TMBound idx) of
                    Right tm -> pure tm
                    Left msg -> liftEither (Left ("explicit term argument `" <> name <> "`: " <> msg))
                Right Nothing -> liftEither (Left err)
                Left msg -> liftEither (Left ("explicit term argument `" <> name <> "`: " <> msg))
            _ ->
              liftEither (Left err)
      where
        implicitBoundCandidate ctx expectedSort = do
          expectedNorm <- normalizeObjDeep ttDoc expectedSort
          let candidates =
                [ (idx, sortTy)
                | (idx, sortTy) <- zip [0 :: Int ..] ctx
                , objOwnerMode sortTy == objOwnerMode expectedNorm
                ]
          matching <- fmap catMaybes $ mapM (matches expectedNorm) candidates
          case matching of
            [] -> Right Nothing
            [idx] -> Right (Just idx)
            _ -> Left "ambiguous bound term variable (multiple binder variables share this sort)"

        matches expectedNorm (idx, sortTy) = do
          sortNorm <- normalizeObjDeep ttDoc sortTy
          pure (if sortNorm == expectedNorm then Just idx else Nothing)

    mkGenDiag curTmCtx g attrs bargs dom cod = do
      let (ins, d0) = allocPorts dom (emptyDiagram mode curTmCtx)
      let (outs, d1) = allocPorts cod d0
      d2 <- addEdgePayload (PGen g attrs bargs) ins outs d1
      let d3 = d2 { dIn = ins, dOut = outs }
      validateDiagram d3
      pure d3

    mkSpliceDiag curTmCtx meta dom cod = do
      let (ins, d0) = allocPorts dom (emptyDiagram mode curTmCtx)
      let (outs, d1) = allocPorts cod d0
      d2 <- addEdgePayload (PSplice meta) ins outs d1
      let d3 = d2 { dIn = ins, dOut = outs }
      validateDiagram d3
      pure d3

    lookupPortTy d pid =
      case diagramPortObj d pid of
        Nothing -> Left "loop: internal missing port type"
        Just ty -> Right ty

    canonicalCtx ttDoc ctx = liftEither (mapM (U.applySubstObj ttDoc U.emptySubst) ctx)

    applySubstCtxDoc ttDoc subst ctx = liftEither (U.applySubstCtx ttDoc subst ctx)

    applySubstBinderSig ttDoc subst bs = do
      tmCtx' <- applySubstCtxDoc ttDoc subst (bsTmCtx bs)
      dom' <- applySubstCtxDoc ttDoc subst (bsDom bs)
      cod' <- applySubstCtxDoc ttDoc subst (bsCod bs)
      pure bs { bsTmCtx = tmCtx', bsDom = dom', bsCod = cod' }

    allocPorts [] diag = ([], diag)
    allocPorts (ty:rest) diag =
      let (pid, diag1) = freshPort ty diag
          (pids, diag2) = allocPorts rest diag1
      in (pid:pids, diag2)

    lookupTerm env' name =
      case M.lookup name (meTerms env') of
        Nothing -> Left ("unknown term: " <> name)
        Just term -> Right term

    renderModeName (ModeName name) = name

    lookupDoctrine env' name =
      case M.lookup name (meDoctrines env') of
        Nothing -> Left ("Unknown doctrine: " <> name)
        Just doc' -> Right doc'

metaVarsIn :: RawDiagExpr -> [Text]
metaVarsIn expr =
  case expr of
    RDId _ -> []
    RDMetaVar name -> [name]
    RDGen _ _ _ mBinderArgs ->
      case mBinderArgs of
        Nothing -> []
        Just args -> concatMap binderArgMetaVars args
    RDTermRef _ -> []
    RDSplice _ -> []
    RDBox _ inner -> metaVarsIn inner
    RDLoop inner -> metaVarsIn inner
    RDMap _ inner -> metaVarsIn inner
    RDComp a b -> metaVarsIn a <> metaVarsIn b
    RDTensor a b -> metaVarsIn a <> metaVarsIn b
  where
    binderArgMetaVars barg =
      case barg of
        RBAExpr d -> metaVarsIn d
        RBAMeta _ -> []

ensureLinearMetaVars :: RawDiagExpr -> Either Text ()
ensureLinearMetaVars expr =
  case firstDup (metaVarsIn expr) of
    Nothing -> Right ()
    Just name ->
      Left
        ( "diagram metavariable `?"
            <> name
            <> "` used more than once in the same diagram; this language is linear at the diagram level. Use explicit duplication (e.g. `dup`) in a cartesian/affine mode if you intend sharing."
        )
  where
    firstDup = go S.empty
    go _ [] = Nothing
    go seen (x:xs)
      | x `S.member` seen = Just x
      | otherwise = go (S.insert x seen) xs

lookupGen :: Doctrine -> ModeName -> GenName -> Either Text GenDecl
lookupGen doc mode name =
  case M.lookup mode (dGens doc) >>= M.lookup name of
    Nothing -> Left ("unknown generator: " <> renderGen name <> " @" <> renderMode mode)
    Just gd -> Right gd
  where
    renderMode (ModeName m) = m
    renderGen (GenName g) = g

unifyBoundary :: TypeTheory -> S.Set TmVar -> S.Set TmVar -> Context -> Context -> Diagram -> Either Text Diagram
unifyBoundary tt rigidTy rigidTm dom cod diag = do
  domDiag <- diagramDom diag
  let flexTy0 = S.difference (freeObjVarsDiagram diag) rigidTy
  let flexTm0 = S.difference (freeTmVarsDiagram diag) rigidTm
  let flex0 = S.union flexTy0 flexTm0
  s1 <- U.unifyCtx tt (dTmCtx diag) flex0 domDiag dom
  diag1 <- applySubstDiagram tt s1 diag
  codDiag <- diagramCod diag1
  let flexTy1 = S.difference (freeObjVarsDiagram diag1) rigidTy
  let flexTm1 = S.difference (freeTmVarsDiagram diag1) rigidTm
  let flex1 = S.union flexTy1 flexTm1
  s2 <- U.unifyCtx tt (dTmCtx diag1) flex1 codDiag cod
  applySubstDiagram tt s2 diag1

elabGenAttrs :: Doctrine -> GenDecl -> Maybe [RawAttrArg] -> Either Text AttrMap
elabGenAttrs doc gen mArgs =
  case gdAttrs gen of
    [] ->
      case mArgs of
        Nothing -> Right M.empty
        Just _ -> Left "generator does not accept attribute arguments"
    fields -> do
      args <- maybe (Left "missing generator attribute arguments") Right mArgs
      normalized <- normalizeAttrArgs fields args
      (attrs, _) <- foldM elabOne (M.empty, M.empty) normalized
      Right attrs
  where
    elabOne (attrs, varSorts) (fieldName, fieldSort, rawTerm) = do
      (term, varSorts') <- elabRawAttrTerm doc fieldSort varSorts rawTerm
      Right (M.insert fieldName term attrs, varSorts')

normalizeAttrArgs :: [(AttrName, AttrSort)] -> [RawAttrArg] -> Either Text [(AttrName, AttrSort, RawAttrTerm)]
normalizeAttrArgs fields args =
  case (namedArgs, positionalArgs) of
    (_:_, _:_) -> Left "generator attribute arguments must be either all named or all positional"
    (_:_, []) -> normalizeNamed namedArgs
    ([], _) -> normalizePos positionalArgs
  where
    namedArgs = [ (name, term) | RAName name term <- args ]
    positionalArgs = [ term | RAPos term <- args ]
    fieldNames = map fst fields
    normalizeNamed named = do
      ensureDistinct "duplicate generator attribute argument" (map fst named)
      if length named /= length fields
        then Left "generator attribute argument mismatch"
        else Right ()
      if S.fromList (map fst named) == S.fromList fieldNames
        then Right ()
        else Left "generator attribute arguments must cover exactly the declared fields"
      let namedMap = M.fromList named
      traverse
        (\(fieldName, fieldSort) ->
          case M.lookup fieldName namedMap of
            Nothing -> Left "missing generator attribute argument"
            Just term -> Right (fieldName, fieldSort, term))
        fields
    normalizePos positional =
      if length positional /= length fields
        then Left "generator attribute argument mismatch"
        else Right [ (fieldName, fieldSort, term) | ((fieldName, fieldSort), term) <- zip fields positional ]

elabRawAttrTerm
  :: Doctrine
  -> AttrSort
  -> M.Map Text AttrSort
  -> RawAttrTerm
  -> Either Text (AttrTerm, M.Map Text AttrSort)
elabRawAttrTerm doc expectedSort varSorts rawTerm =
  case rawTerm of
    RATVar name ->
      case M.lookup name varSorts of
        Nothing ->
          Right (ATVar (AttrVar name expectedSort), M.insert name expectedSort varSorts)
        Just sortName ->
          if sortName == expectedSort
            then Right (ATVar (AttrVar name expectedSort), varSorts)
            else Left "attribute variable used with conflicting sorts"
    RATInt n -> do
      ensureLiteralKind LKInt
      Right (ATLit (ALInt n), varSorts)
    RATString s -> do
      ensureLiteralKind LKString
      Right (ATLit (ALString s), varSorts)
    RATBool b -> do
      ensureLiteralKind LKBool
      Right (ATLit (ALBool b), varSorts)
  where
    ensureLiteralKind kind = do
      decl <-
        case M.lookup expectedSort (dAttrSorts doc) of
          Nothing -> Left "unknown attribute sort"
          Just d -> Right d
      case asLitKind decl of
        Just allowed | allowed == kind -> Right ()
        _ -> Left "attribute sort does not admit this literal kind"

ensureAcyclicMode :: Doctrine -> ModeName -> Diagram -> Either Text ()
ensureAcyclicMode doc mode diag =
  if modeIsAcyclic doc mode
    then do
      _ <- topologicalEdges diag
      mapM_ checkInner (IM.elems (dEdges diag))
    else Right ()
  where
    checkInner edge =
      case ePayload edge of
        PBox _ inner -> ensureAcyclicMode doc mode inner
        PFeedback inner -> ensureAcyclicMode doc mode inner
        _ -> Right ()

topologicalEdges :: Diagram -> Either Text [Edge]
topologicalEdges diag =
  if IM.null edgeTable
    then Right []
    else
      if length orderedIds == IM.size edgeTable
        then mapM lookupEdge orderedIds
        else Left "acyclic mode violation: diagram contains a cycle"
  where
    edgeTable = dEdges diag
    edgeIds = map eId (IM.elems edgeTable)

    deps0 = M.fromList [(eid, depsFor eid) | eid <- edgeIds]
    dependents = foldl insertDeps M.empty (M.toList deps0)

    insertDeps acc (eid, deps) =
      S.foldl' (\m dep -> M.insertWith S.union dep (S.singleton eid) m) acc deps

    depsFor eid =
      case findEdge eid of
        Nothing -> S.empty
        Just edge ->
          S.fromList
            [ prod
            | p <- eIns edge
            , Just (Just prod) <- [IM.lookup (portInt p) (dProd diag)]
            ]

    ready0 =
      S.fromList
        [ eid
        | (eid, deps) <- M.toList deps0
        , S.null deps
        ]

    orderedIds = go ready0 deps0 []

    go ready deps acc =
      case S.lookupMin ready of
        Nothing -> reverse acc
        Just eid ->
          let readyRest = S.deleteMin ready
              out = M.findWithDefault S.empty eid dependents
              (deps', ready') = S.foldl' (dropDep eid) (deps, readyRest) out
           in go ready' deps' (eid : acc)

    dropDep done (deps, ready) target =
      let old = M.findWithDefault S.empty target deps
          new = S.delete done old
          deps' = M.insert target new deps
          ready' = if S.null new then S.insert target ready else ready
       in (deps', ready')

    findEdge eid =
      let EdgeId k = eid
       in IM.lookup k edgeTable

    lookupEdge eid =
      case findEdge eid of
        Nothing -> Left "internal error: missing edge"
        Just edge -> Right edge

    portInt (PortId i) = i

-- Freshening monad

newtype Fresh a = Fresh (Int -> Either Text (a, Int))

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

freshTySubst :: Doctrine -> [TmVar] -> Fresh (M.Map TmVar Obj)
freshTySubst doc vars = do
  pairs <- mapM (freshTyVar doc) vars
  pure (M.fromList pairs)

freshTmSubst :: TypeTheory -> [Obj] -> [TmVar] -> Fresh (M.Map TmVar TermDiagram)
freshTmSubst ttDoc tmCtx vars = do
  pairs <- mapM (freshTmVar ttDoc tmCtx) vars
  pure (M.fromList pairs)

extractFreshTyVars :: [TmVar] -> M.Map TmVar Obj -> Either Text [TmVar]
extractFreshTyVars vars subst =
  mapM lookupVar vars
  where
    lookupVar v =
      case M.lookup v subst of
        Just (OVar v') -> Right v'
        _ -> Left "internal error: expected fresh type variable"

extractFreshTmVars :: [TmVar] -> M.Map TmVar TermDiagram -> Either Text [TmVar]
extractFreshTmVars vars subst =
  mapM lookupVar vars
  where
    lookupVar v =
      case M.lookup v subst of
        Just tm ->
          case metaOnly tm of
            Just v' -> Right v'
            Nothing -> Left "internal error: expected fresh term variable"
        _ -> Left "internal error: expected fresh term variable"

    metaOnly (TermDiagram diag) =
      case (IM.elems (dEdges diag), dOut diag) of
        ([edge], [outBoundary]) ->
          case (ePayload edge, eOuts edge) of
            (PTmMeta v, [outPid]) | outPid == outBoundary -> Just v
            _ -> Nothing
        _ -> Nothing

freshTyVar :: Doctrine -> TmVar -> Fresh (TmVar, Obj)
freshTyVar doc v = do
  n <- freshInt
  let name = ovName v <> T.pack ("#" <> show n)
  let fresh = v { tmvName = name }
  ownerMode <- liftEither (ownerModeForTypeMeta doc v)
  pure (v, Obj { objOwnerMode = ownerMode, objCode = CTMeta fresh })

freshTmVar :: TypeTheory -> [Obj] -> TmVar -> Fresh (TmVar, TermDiagram)
freshTmVar ttDoc tmCtx v = do
  n <- freshInt
  let name = tmvName v <> T.pack ("#" <> show n)
  let fresh = TmVar { tmvName = name, tmvSort = tmvSort v, tmvScope = max (tmvScope v) (length tmCtx), tmvOwnerMode = Nothing }
  tm <- liftEither (termExprToDiagramChecked ttDoc tmCtx (tmvSort fresh) (TMVar fresh))
  pure (v, tm)

freshInt :: Fresh Int
freshInt = Fresh (\n -> Right (n, n + 1))

liftEither :: Either Text a -> Fresh a
liftEither (Left err) = Fresh (\_ -> Left err)
liftEither (Right a) = pure a
