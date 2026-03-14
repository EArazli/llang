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
  , elabDiagExprInScope
  , elabDiagExprWith
  , elabDiagExprWithInScope
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
  ( RawPolyGenMap(..)
  , RawPolyModeMap(..)
  , RawPolyModalityMap(..)
  , RawPolyMorphism(..)
  , RawPolyMorphismItem(..)
  , RawPolyTypeMap(..)
    )
import Strat.Frontend.Env (ModuleEnv(..))
import Strat.Poly.DSL.Elab.Diag
  ( BinderMetaMode(..)
  , elabDiagExpr
  , elabDiagExprInScope
  , elabDiagExprWith
  , elabDiagExprWithInScope
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
  ( buildTypeTemplateBinders
  , elabObjExpr
  , ownerModeForTypeMeta
  )
import Strat.Poly.Diagram
import Strat.Poly.Doctrine
import Strat.Poly.Graph
  ( BinderArg(..)
  , BinderMetaVar(..)
  , EdgePayload(..)
  , addEdgePayload
  , emptyDiagram
  , freshPort
  , validateDiagram
  )
import Strat.Poly.ModeTheory
import Strat.Poly.Morphism
import Strat.Poly.Names
import Strat.Poly.Obj
import Strat.Pipeline (DerivedDoctrine(..))
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
  typeMap <- foldM (addTypeMap src srcCtorTables tgt modeMap) M.empty [ t | RPMType t <- rpmItems raw ]
  let mor0 = Morphism
        { morName = rpmName raw
        , morSrc = src
        , morTgt = tgt
        , morIsCoercion = not (null coercionFlags)
        , morModeMap = modeMap
        , morModMap = modMap
        , morTypeMap = typeMap
        , morGenMap = M.empty
        , morCheck = checkMode
        , morPolicy = policy
        }
  explicitGenMap <- foldM (addGenMap src tgt ttSrc ttTgt tgtCtorTables modeMap mor0) M.empty [ g | RPMGen g <- rpmItems raw ]
  autoFillNames <- reflectedAutoFillNames env src
  genMap <- autoFillImplicitGenMaps autoFillNames src srcCtorTables tgt ttSrc ttTgt tgtCtorTables modeMap mor0 explicitGenMap
  ensureAllGenMapped src srcCtorTables genMap
  let mor = Morphism
        { morName = rpmName raw
        , morSrc = src
        , morTgt = tgt
        , morIsCoercion = not (null coercionFlags)
        , morModeMap = modeMap
        , morModMap = modMap
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
      (tmplParams, tyVarsTgt, tmVarsTgt) <- buildTypeTemplateBinders tgt modeMap srcParams (rpmtParams decl)
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
      (diag0, _) <- elabDiagExprWith env tgt modeTgt [] tyVarsTgt tmVarsTgt binderSigs0 BMUse True False (rpmgRhs decl)
      let domSrc = gdPlainDom gen
      let codSrc = gdCod gen
      domTgt <- mapM (applyMorphismTyWithCaches ttSrc ttTgt tgtTables mor0) domSrc
      codTgt <- mapM (applyMorphismTyWithCaches ttSrc ttTgt tgtTables mor0) codSrc
      let rigidTy = S.fromList tyVarsTgt
      let rigidTm = S.fromList tmVarsTgt
      diag <- unifyBoundary ttTgt rigidTy rigidTm domTgt codTgt diag0
      let freeVars = freeVarsDiagram diag
      let allowedVars = S.fromList (tyVarsTgt <> tmVarsTgt)
      if S.isSubsetOf freeVars allowedVars
        then Right ()
        else Left "morphism: generator mapping uses undeclared type variables"
      if S.isSubsetOf freeVars allowedVars
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
    autoFillImplicitGenMaps autoFillNames src srcTables tgt ttSrc ttTgt tgtTables modeMap mor0 mp =
      foldM addMissing mp (allAutoMappableGens autoFillNames src srcTables)
      where
        addMissing acc (modeSrc, gen)
          | M.member (modeSrc, gdName gen) acc = Right acc
          | otherwise =
              case inferImplicitGenImage autoFillNames tgt ttSrc ttTgt tgtTables modeMap mor0 modeSrc gen of
                Nothing -> Right acc
                Just image -> Right (M.insert (modeSrc, gdName gen) image acc)
    inferImplicitGenImage autoFillNames tgt ttSrc ttTgt tgtTables modeMap mor0 modeSrc gen
      | gdName gen `S.notMember` autoFillNames = Nothing
      | otherwise =
          either (const Nothing) id $ do
            modeTgt <- lookupModeMap modeMap modeSrc
            targetGen <- lookupGeneratorMaybe tgt modeTgt (gdName gen)
            case targetGen of
              Nothing -> Right Nothing
              Just targetGen' -> do
                mappedParams <- mapM (mapParam ttSrc ttTgt tgtTables mor0) (gdParams gen)
                mappedDom <- mapM (mapInputShape ttSrc ttTgt tgtTables mor0) (gdDom gen)
                mappedCod <- mapM (applyMorphismTyWithCaches ttSrc ttTgt tgtTables mor0) (gdCod gen)
                if generatorParamsCompatible mappedParams (gdParams targetGen')
                    && mappedDom == gdDom targetGen'
                    && mappedCod == gdCod targetGen'
                    && gdLiteralKind gen == gdLiteralKind targetGen'
                  then Just <$> mkImplicitGenImage modeTgt (gdName targetGen') mappedParams mappedDom mappedCod
                  else Right Nothing
    allAutoMappableGens autoFillNames src ctorTables =
      [ (mode, gd)
      | (mode, table) <- M.toList (dGens src)
      , gd <- M.elems table
      , not (isTypeDeclGenNameInTables src ctorTables mode (ObjName (renderGenName (gdName gd))))
      , gdName gd `S.member` autoFillNames
      ]
    lookupGeneratorMaybe doc mode name =
      Right (M.lookup mode (dGens doc) >>= M.lookup name)
    mapParam ttSrc ttTgt tgtTables mor param =
      case param of
        GP_Ty v -> GP_Ty <$> mapTyVarMode ttSrc ttTgt tgtTables mor v
        GP_Tm v -> GP_Tm <$> mapTmVarSort ttSrc ttTgt tgtTables mor v
    mapInputShape ttSrc ttTgt tgtTables mor shape =
      case shape of
        InPort ty -> InPort <$> applyMorphismTyWithCaches ttSrc ttTgt tgtTables mor ty
        InBinder sig -> InBinder <$> applyMorphismBinderSigWithTables tgtTables mor sig
    generatorParamsCompatible xs ys =
      length xs == length ys && and (zipWith paramCompatible xs ys)
    paramCompatible srcParam tgtParam =
      case (srcParam, tgtParam) of
        (GP_Ty srcVar, GP_Ty tgtVar) ->
          tmVarOwner srcVar == tmVarOwner tgtVar
            && tmvSort srcVar == tmvSort tgtVar
        (GP_Tm srcVar, GP_Tm tgtVar) ->
          tmvSort srcVar == tmvSort tgtVar
        _ -> False
    mkImplicitGenImage mode genName params dom cod = do
      args <- mapM paramArg params
      let binderSlots = [ () | InBinder _ <- dom ]
          bargs =
            [ BAMeta (BinderMetaVar ("b" <> T.pack (show i)))
            | i <- [0 .. length binderSlots - 1]
            ]
          portsDom = [ ty | InPort ty <- dom ]
          binderSigs =
            M.fromList
              [ (BinderMetaVar ("b" <> T.pack (show i)), sig)
              | (i, sig) <- zip [0 :: Int ..] [ sig | InBinder sig <- dom ]
              ]
          (ins, diag0) = allocPorts portsDom (emptyDiagram mode [])
          (outs, diag1) = allocPorts cod diag0
      diag2 <- addEdgePayload (PGen genName args bargs) ins outs diag1
      let diag3 = diag2 { dIn = ins, dOut = outs }
      validateDiagram diag3
      pure (GenImage diag3 binderSigs)
      where
        allocPorts [] diag = ([], diag)
        allocPorts (ty:rest) diag =
          let (pid, diag1) = freshPort ty diag
              (pids, diag2) = allocPorts rest diag1
           in (pid : pids, diag2)
        paramArg param =
          case param of
            GP_Ty v -> Right (CAObj (OVar v))
            GP_Tm v -> CATm <$> tmVarDiagram v
        tmVarDiagram v = do
          let (outPid, d0) = freshPort (tmvSort v) (emptyDiagram (objOwnerMode (tmvSort v)) [])
          d1 <- addEdgePayload (PTmMeta v) [] [outPid] d0
          let d2 = d1 { dOut = [outPid] }
          validateDiagram d2
          pure (TermDiagram d2)
    reflectedAutoFillNames env' srcDoc =
      case M.lookup (dName srcDoc) (meDerivedDoctrines env') of
        Just DerivedReflectQuotation { ddBase = baseName } -> do
          baseDoc <-
            case M.lookup baseName (meDoctrines env') of
              Nothing -> Left ("Unknown doctrine: " <> baseName)
              Just doc -> Right doc
          baseTables <- deriveCtorTables baseDoc
          let baseReflectedNames =
                S.fromList
                  [ GenName ("q_" <> renderGenName (gdName gd))
                  | (_, table) <- M.toList (dGens baseDoc)
                  , gd <- M.elems table
                  , not
                      ( isTypeDeclGenNameInTables
                          baseDoc
                          baseTables
                          (gdMode gd)
                          (ObjName (renderGenName (gdName gd)))
                      )
                  ]
              supportNames =
                S.fromList
                  [ GenName "digit0"
                  , GenName "digit1"
                  , GenName "digit2"
                  , GenName "digit3"
                  , GenName "digit4"
                  , GenName "digit5"
                  , GenName "digit6"
                  , GenName "digit7"
                  , GenName "digit8"
                  , GenName "digit9"
                  , GenName "refId_nil"
                  , GenName "refId_cons"
                  , GenName "refId_label"
                  , GenName "refIds_nil"
                  , GenName "refIds_cons"
                  , GenName "q_begin"
                  , GenName "q_end"
                  , GenName "q_res_box"
                  , GenName "q_res_feedback"
                  , GenName "q_provider"
                  , GenName "q_module_ref"
                  ]
              sourceNames =
                S.fromList
                  [ gdName gd
                  | table <- M.elems (dGens srcDoc)
                  , gd <- M.elems table
                  ]
          pure (S.intersection sourceNames (baseReflectedNames `S.union` supportNames))
        Nothing -> Right S.empty
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
