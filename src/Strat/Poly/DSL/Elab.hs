{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.DSL.Elab
  ( elabPolyDoctrine
  , elabPolyMorphism
  , elabDiagExpr
  , parsePolicy
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import qualified Data.Set as S
import Data.Maybe (catMaybes)
import Control.Monad (foldM, when)
import Strat.DSL.AST (RawPolyMorphism(..), RawPolyMorphismItem(..), RawPolyTypeMap(..), RawPolyGenMap(..), RawPolyModeMap(..), RawPolyModalityMap(..), RawPolyAttrSortMap(..))
import Strat.Poly.DSL.AST
import Strat.Poly.Doctrine
import Strat.Poly.Diagram
import Strat.Poly.Graph (emptyDiagram, freshPort, setPortLabel, addEdgePayload, Edge(..), EdgeId(..), PortId(..), EdgePayload(..), BinderArg(..), BinderMetaVar(..), validateDiagram, diagramPortType)
import Strat.Poly.ModeTheory
import Strat.Poly.Names
import Strat.Poly.TypeExpr
import qualified Strat.Poly.UnifyTy as U
import Strat.Poly.TypeTheory (TypeTheory, TmFunSig(..))
import Strat.Poly.TypeNormalize (normalizeTypeDeep)
import Strat.Poly.Attr
import Strat.Poly.Morphism
import Strat.Poly.ModAction (applyModExpr, validateActionSemantics)
import Strat.Frontend.Env (ModuleEnv(..), TermDef(..))
import Strat.Frontend.Coerce (coerceDiagramTo)
import Strat.Poly.Cell2 (Cell2(..))
import Strat.Common.Rules (RewritePolicy(..))
import Strat.Poly.TermExpr (TermExpr(..), termExprToDiagram)

elabPolyMorphism :: ModuleEnv -> RawPolyMorphism -> Either Text Morphism
elabPolyMorphism env raw = do
  src <- lookupPolyDoctrine env (rpmSrc raw)
  tgt <- lookupPolyDoctrine env (rpmTgt raw)
  let checkName = maybe "all" id (rpmCheck raw)
  checkMode <- parseMorphismCheck checkName
  let policyName = maybe "UseStructuralAsBidirectional" id (rpmPolicy raw)
  policy <- parsePolicy policyName
  let fuel = maybe 50 id (rpmFuel raw)
  let coercionFlags = [() | RPMCoercion <- rpmItems raw]
  when (length coercionFlags > 1) (Left "morphism: duplicate coercion flag")
  modeMap <- buildModeMap src tgt [ m | RPMMode m <- rpmItems raw ]
  modMap <- buildModMap src tgt modeMap [ mm | RPMModality mm <- rpmItems raw ]
  attrSortMap <- buildAttrSortMap src tgt [ a | RPMAttrSort a <- rpmItems raw ]
  typeMap <- foldM (addTypeMap src tgt modeMap) M.empty [ t | RPMType t <- rpmItems raw ]
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
        , morFuel = fuel
        }
  genMap <- foldM (addGenMap src tgt modeMap mor0) M.empty [ g | RPMGen g <- rpmItems raw ]
  ensureAllGenMapped src genMap
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
    mapTyVarMode modeMap v = do
      mode' <- lookupModeMap modeMap (tvMode v)
      pure v { tvMode = mode' }
    mapTmVarSort mor v = do
      sort' <- applyMorphismTy mor (tmvSort v)
      pure v { tmvSort = sort' }
    addTypeMap src tgt modeMap mp decl = do
      let modeSrc = ModeName (rpmtSrcMode decl)
      let modeTgtDecl = ModeName (rpmtTgtMode decl)
      ensureMode src modeSrc
      ensureMode tgt modeTgtDecl
      modeTgtExpected <- lookupModeMap modeMap modeSrc
      if modeTgtDecl /= modeTgtExpected
        then Left "morphism: target mode does not match mode map"
        else Right ()
      let name = TypeName (rpmtSrcType decl)
      let ref = TypeRef modeSrc name
      sig <- lookupTypeSig src ref
      (tmplParams, tyVarsTgt, tmVarsTgt) <- buildTypeTemplateParams tgt modeMap (tsParams sig) (rpmtParams decl)
      tgtExpr <- elabTypeExpr tgt tyVarsTgt tmVarsTgt M.empty (rpmtTgtType decl)
      if typeMode tgtExpr /= modeTgtDecl
        then Left ("morphism: target type expression mode mismatch (expected " <> rpmtTgtMode decl <> ")")
        else Right ()
      let key = TypeRef modeSrc name
      if M.member key mp
        then Left "morphism: duplicate type mapping"
        else Right (M.insert key (TypeTemplate tmplParams tgtExpr) mp)
    addGenMap src tgt modeMap mor0 mp decl = do
      let modeSrc = ModeName (rpmgMode decl)
      ensureMode src modeSrc
      modeTgt <- lookupModeMap modeMap modeSrc
      ensureMode tgt modeTgt
      gen <- lookupGen src modeSrc (GenName (rpmgSrcGen decl))
      tyVarsTgt <- mapM (mapTyVarMode modeMap) (gdTyVars gen)
      tmVarsTgt <- mapM (mapTmVarSort mor0) (gdTmVars gen)
      binderSigs0 <- buildBinderHoleSigs mor0 gen
      (diag0, _) <- elabDiagExprWith env tgt modeTgt [] tyVarsTgt tmVarsTgt binderSigs0 BMUse True (rpmgRhs decl)
      let domSrc = gdPlainDom gen
      let codSrc = gdCod gen
      domTgt <- mapM (applyMorphismTy mor0) domSrc
      codTgt <- mapM (applyMorphismTy mor0) codSrc
      let rigidTy = S.fromList tyVarsTgt
      let rigidTm = S.fromList tmVarsTgt
      let ttTgt = doctrineTypeTheory tgt
      diag <- unifyBoundary ttTgt rigidTy rigidTm domTgt codTgt diag0
      let freeTy = freeTyVarsDiagram diag
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
    buildBinderHoleSigs mor gen =
      let slots = [ bs | InBinder bs <- gdDom gen ]
          holes = [ BinderMetaVar ("b" <> T.pack (show i)) | i <- [0 .. length slots - 1] ]
      in fmap M.fromList (mapM (mapOne mor) (zip holes slots))
    mapOne mor (hole, sig) = do
      tmCtx' <- mapM (applyMorphismTy mor) (bsTmCtx sig)
      dom' <- mapM (applyMorphismTy mor) (bsDom sig)
      cod' <- mapM (applyMorphismTy mor) (bsCod sig)
      pure (hole, sig { bsTmCtx = tmCtx', bsDom = dom', bsCod = cod' })
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
  validateActionSemantics doc
  pure doc

seedDoctrine :: Text -> Maybe Doctrine -> Doctrine
seedDoctrine name base =
  case base of
    Nothing -> Doctrine
      { dName = name
      , dModes = emptyModeTheory
      , dAcyclicModes = S.empty
      , dAttrSorts = M.empty
      , dTypes = M.empty
      , dGens = M.empty
      , dCells2 = []
      , dActions = M.empty
      , dObligations = []
      }
    Just doc -> doc { dName = name, dAttrSorts = dAttrSorts doc }

elabPolyItem :: ModuleEnv -> Doctrine -> RawPolyItem -> Either Text Doctrine
elabPolyItem env doc item =
  case item of
    RPMode decl -> do
      let mode = ModeName (rmdName decl)
      mt' <- addMode mode (dModes doc)
      let acyclic' =
            if rmdAcyclic decl
              then S.insert mode (dAcyclicModes doc)
              else dAcyclicModes doc
      pure doc { dModes = mt', dAcyclicModes = acyclic' }
    RPModality decl -> do
      let modDecl =
            ModDecl
              { mdName = ModName (rmodName decl)
              , mdSrc = ModeName (rmodSrc decl)
              , mdTgt = ModeName (rmodTgt decl)
              }
      mt' <- addModDecl modDecl (dModes doc)
      pure doc { dModes = mt' }
    RPModEq decl -> do
      lhs <- elabRawModExpr (dModes doc) (rmeLHS decl)
      rhs <- elabRawModExpr (dModes doc) (rmeRHS decl)
      mt' <- addModEqn (ModEqn lhs rhs) (dModes doc)
      pure doc { dModes = mt' }
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
              , maFuel = 50
              }
      if M.member modName (dActions doc)
        then Left "duplicate action declaration"
        else pure doc { dActions = M.insert modName action (dActions doc) }
    RPObligation decl -> do
      let mode = ModeName (rodMode decl)
      ensureMode doc mode
      if rodForGen decl
        then do
          if null (rodVars decl) && null (rodDom decl) && null (rodCod decl)
            then pure ()
            else Left "obligation for_gen does not accept explicit vars or boundary signature"
          let gens = M.elems (M.findWithDefault M.empty mode (dGens doc))
          obls <- mapM (elabForGenObligation env doc decl mode) gens
          pure doc { dObligations = dObligations doc <> obls }
        else do
          (tyVars, tmVars, _sigParams) <- elabParamDecls doc mode (rodVars decl)
          dom <- elabContext doc mode tyVars tmVars M.empty (rodDom decl)
          cod <- elabContext doc mode tyVars tmVars M.empty (rodCod decl)
          lhs <- elabObligationExpr env doc mode tyVars tmVars Nothing (rodLHS decl)
          rhs <- elabObligationExpr env doc mode tyVars tmVars Nothing (rodRHS decl)
          let rigidTy = S.fromList tyVars
          let rigidTm = S.fromList tmVars
          let tt = doctrineTypeTheory doc
          lhs' <- unifyBoundary tt rigidTy rigidTm dom cod lhs
          rhs' <- unifyBoundary tt rigidTy rigidTm dom cod rhs
          let obl =
                ObligationDecl
                  { obName = rodName decl
                  , obTyVars = tyVars
                  , obTmVars = tmVars
                  , obLHS = lhs'
                  , obRHS = rhs'
                  , obPolicy = UseStructuralAsBidirectional
                  , obFuel = 50
                  }
          pure doc { dObligations = dObligations doc <> [obl] }
    RPAttrSort decl -> do
      let sortName = AttrSort (rasName decl)
      litKind <- mapM parseAttrLitKind (rasKind decl)
      if M.member sortName (dAttrSorts doc)
        then Left "duplicate attribute sort name"
        else do
          let sortDecl = AttrSortDecl { asName = sortName, asLitKind = litKind }
          pure doc { dAttrSorts = M.insert sortName sortDecl (dAttrSorts doc) }
    RPType decl -> do
      let mode = ModeName (rptMode decl)
      ensureMode doc mode
      let tname = TypeName (rptName decl)
      (_tyVars, _ixVars, sigParams) <- elabParamDecls doc mode (rptVars decl)
      let sig = TypeSig { tsParams = sigParams }
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
      (tyVars, tmVars, _sigParams) <- elabParamDecls doc mode (rpgVars decl)
      attrs <- mapM (resolveAttrField doc) (rpgAttrs decl)
      ensureDistinct "duplicate generator attribute field name" (map fst attrs)
      dom <- elabInputShapes doc mode tyVars tmVars (rpgDom decl)
      cod <- elabContext doc mode tyVars tmVars M.empty (rpgCod decl)
      let gen = GenDecl
            { gdName = gname
            , gdMode = mode
            , gdTyVars = tyVars
            , gdTmVars = tmVars
            , gdDom = dom
            , gdCod = cod
            , gdAttrs = attrs
            }
      let table = M.findWithDefault M.empty mode (dGens doc)
      if M.member gname table
        then Left "duplicate generator name"
        else do
          let table' = M.insert gname gen table
          let gens' = M.insert mode table' (dGens doc)
          pure doc { dGens = gens' }
    RPData decl -> do
      let modeName = rpdTyMode decl
      let mode = ModeName modeName
      ensureMode doc mode
      let ctorNames = map rpdCtorName (rpdCtors decl)
      ensureDistinct "data: duplicate constructor name" ctorNames
      let existing = M.findWithDefault M.empty mode (dGens doc)
      case [c | c <- ctorNames, M.member (GenName c) existing] of
        (c:_) -> Left ("data: constructor name conflicts with generator " <> c)
        [] -> Right ()
      let typeDecl = RawPolyTypeDecl
            { rptName = rpdTyName decl
            , rptVars = map RPDType (rpdTyVars decl)
            , rptMode = modeName
            }
      let ctors = map (mkCtor modeName (rpdTyName decl) (rpdTyVars decl)) (rpdCtors decl)
      foldM (elabPolyItem env) doc (RPType typeDecl : map RPGen ctors)
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
      let tt = doctrineTypeTheory doc
      lhs' <- unifyBoundary tt rigidTy rigidTm dom cod lhs
      rhs' <- unifyBoundary tt rigidTy rigidTm dom cod rhs
      let free = S.union (freeTyVarsDiagram lhs') (freeTyVarsDiagram rhs')
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
      pure doc { dCells2 = dCells2 doc <> [cell] }
      where
        withRule action =
          case action of
            Left err -> Left ("rule " <> rprName decl <> ": " <> err)
            Right x -> Right x

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
  let typeRef = RawTypeRef { rtrMode = Just modeName, rtrName = tyName }
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

elabForGenObligation
  :: ModuleEnv
  -> Doctrine
  -> RawObligationDecl
  -> ModeName
  -> GenDecl
  -> Either Text ObligationDecl
elabForGenObligation env doc decl mode gen = do
  if gdMode gen == mode
    then Right ()
    else Left "obligation for_gen: internal generator mode mismatch"
  genDiag <- mkForGenDiag mode gen
  lhs0 <- elabObligationExpr env doc mode (gdTyVars gen) (gdTmVars gen) (Just genDiag) (rodLHS decl)
  rhs0 <- elabObligationExpr env doc mode (gdTyVars gen) (gdTmVars gen) (Just genDiag) (rodRHS decl)
  dom <- diagramDom genDiag
  cod <- diagramCod genDiag
  let rigidTy = S.fromList (gdTyVars gen)
  let rigidTm = S.fromList (gdTmVars gen)
  let tt = doctrineTypeTheory doc
  lhs <- unifyBoundary tt rigidTy rigidTm dom cod lhs0
  rhs <- unifyBoundary tt rigidTy rigidTm dom cod rhs0
  pure
    ObligationDecl
      { obName = rodName decl <> "[" <> renderGenName (gdName gen) <> "]"
      , obTyVars = gdTyVars gen
      , obTmVars = gdTmVars gen
      , obLHS = lhs
      , obRHS = rhs
      , obPolicy = UseStructuralAsBidirectional
      , obFuel = 50
      }
  where
    renderGenName (GenName n) = n

elabObligationExpr
  :: ModuleEnv
  -> Doctrine
  -> ModeName
  -> [TyVar]
  -> [TmVar]
  -> Maybe Diagram
  -> RawOblExpr
  -> Either Text Diagram
elabObligationExpr env doc mode tyVars tmVars mGen expr =
  case expr of
    ROEDiag rawDiag ->
      elabObligationDiag env doc mode tmCtx tyVars tmVars rawDiag
    ROEMap rawMe innerExpr -> do
      me <- elabRawModExpr (dModes doc) rawMe
      inner <- elabObligationExpr env doc (meSrc me) tyVars tmVars mGen innerExpr
      mapped <- applyModExpr doc me inner
      if dMode mapped == mode
        then Right mapped
        else Left "obligation map: mapped diagram mode does not match surrounding expression mode"
    ROEGen ->
      case mGen of
        Nothing -> Left "obligation: @gen is only valid in for_gen obligations"
        Just g -> Right g
    ROELiftDom rawOp ->
      elabLiftedUnary env doc mode tyVars tmVars mGen LiftOverDom rawOp
    ROELiftCod rawOp ->
      elabLiftedUnary env doc mode tyVars tmVars mGen LiftOverCod rawOp
    ROEComp a b -> do
      d1 <- elabObligationExpr env doc mode tyVars tmVars mGen a
      d2 <- elabObligationExpr env doc mode tyVars tmVars mGen b
      compD ttDoc d2 d1
    ROETensor a b -> do
      d1 <- elabObligationExpr env doc mode tyVars tmVars mGen a
      d2 <- elabObligationExpr env doc mode tyVars tmVars mGen b
      tensorD d1 d2
  where
    ttDoc = doctrineTypeTheory doc
    tmCtx = maybe [] dTmCtx mGen

data LiftBoundary
  = LiftOverDom
  | LiftOverCod
  deriving (Eq, Show)

elabLiftedUnary
  :: ModuleEnv
  -> Doctrine
  -> ModeName
  -> [TyVar]
  -> [TmVar]
  -> Maybe Diagram
  -> LiftBoundary
  -> RawDiagExpr
  -> Either Text Diagram
elabLiftedUnary env doc mode tyVars tmVars mGen liftSide rawOp = do
  genDiag <-
    case mGen of
      Nothing ->
        Left "obligation: lift_dom/lift_cod is only valid in for_gen obligations"
      Just g ->
        Right g
  ctx <- case liftSide of
    LiftOverDom -> diagramDom genDiag
    LiftOverCod -> diagramCod genDiag
  ops <- mapM (instantiateAt (dTmCtx genDiag)) ctx
  case ops of
    [] -> Right (idDTm mode (dTmCtx genDiag) [])
    (d0:rest) -> foldM tensorD d0 rest
  where
    ttDoc = doctrineTypeTheory doc
    rigidTy = S.fromList tyVars
    rigidTm = S.fromList tmVars
    sideLabel =
      case liftSide of
        LiftOverDom -> "lift_dom"
        LiftOverCod -> "lift_cod"

    instantiateAt tmCtx argTy = do
      op0 <- elabObligationDiag env doc mode tmCtx tyVars tmVars rawOp
      dom0 <- diagramDom op0
      cod0 <- diagramCod op0
      if length dom0 == 1 && length cod0 == 1
        then unifyBoundary ttDoc rigidTy rigidTm [argTy] cod0 op0
        else Left (sideLabel <> ": operator must be unary ([x] -> [y])")

elabObligationDiag
  :: ModuleEnv
  -> Doctrine
  -> ModeName
  -> [TypeExpr]
  -> [TyVar]
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

ensureMode :: Doctrine -> ModeName -> Either Text ()
ensureMode doc mode =
  if M.member mode (mtModes (dModes doc))
    then Right ()
    else Left "unknown mode"

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

resolveTyVarDecl :: Doctrine -> ModeName -> RawTyVarDecl -> Either Text TyVar
resolveTyVarDecl doc defaultMode decl = do
  mode <- resolveTyVarMode doc defaultMode decl
  pure TyVar { tvName = rtvName decl, tvMode = mode }

elabTmDeclVar :: Doctrine -> [TyVar] -> RawTmVarDecl -> Either Text TmVar
elabTmDeclVar doc tyVars decl = do
  sortTy <- elabTypeExpr doc tyVars [] M.empty (rtvdSort decl)
  pure TmVar { tmvName = rtvdName decl, tmvSort = sortTy, tmvScope = 0 }

elabParamDecls :: Doctrine -> ModeName -> [RawParamDecl] -> Either Text ([TyVar], [TmVar], [ParamSig])
elabParamDecls doc defaultMode params = go [] [] [] params
  where
    go tyAcc tmAcc sigAcc [] = Right (reverse tyAcc, reverse tmAcc, reverse sigAcc)
    go tyAcc tmAcc sigAcc (p:rest) =
      case p of
        RPDType tvDecl -> do
          tv <- resolveTyVarDecl doc defaultMode tvDecl
          let name = tvName tv
          if name `elem` map tvName tyAcc || name `elem` map tmvName tmAcc
            then Left "duplicate parameter name"
            else go (tv:tyAcc) tmAcc (PS_Ty (tvMode tv) : sigAcc) rest
        RPDTerm tmDecl -> do
          let name = rtvdName tmDecl
          if name `elem` map tvName tyAcc || name `elem` map tmvName tmAcc
            then Left "duplicate parameter name"
            else do
              tmVar <- elabTmDeclVar doc tyAcc tmDecl
              go tyAcc (tmVar:tmAcc) (PS_Tm (tmvSort tmVar) : sigAcc) rest

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

buildTypeTemplateParams
  :: Doctrine
  -> M.Map ModeName ModeName
  -> [ParamSig]
  -> [RawParamDecl]
  -> Either Text ([TemplateParam], [TyVar], [TmVar])
buildTypeTemplateParams tgt modeMap sigParams decls = do
  if length sigParams /= length decls
    then Left "morphism: type mapping binder arity mismatch"
    else go [] [] [] (zip sigParams decls)
  where
    go tyAcc tmAcc tmplAcc [] =
      Right (reverse tmplAcc, reverse tyAcc, reverse tmAcc)
    go tyAcc tmAcc tmplAcc ((sigParam, decl):rest) =
      case (sigParam, decl) of
        (PS_Ty srcMode, RPDType tyDecl) -> do
          expectedMode <- lookupMappedMode srcMode
          tyVar <- resolveTyVarDecl tgt expectedMode tyDecl
          ensureFreshName tyAcc tmAcc (tvName tyVar)
          go (tyVar:tyAcc) tmAcc (TPType tyVar:tmplAcc) rest
        (PS_Tm srcSort, RPDTerm tmDecl) -> do
          expectedMode <- lookupMappedMode (typeMode srcSort)
          tmSort <- elabTypeExpr tgt (reverse tyAcc) (reverse tmAcc) M.empty (rtvdSort tmDecl)
          if typeMode tmSort /= expectedMode
            then Left "morphism: type mapping term binder mode mismatch"
            else Right ()
          ensureFreshName tyAcc tmAcc (rtvdName tmDecl)
          let tmVar = TmVar { tmvName = rtvdName tmDecl, tmvSort = tmSort, tmvScope = 0 }
          go tyAcc (tmVar:tmAcc) (TPTm tmVar:tmplAcc) rest
        (PS_Ty _, _) ->
          Left "morphism: type mapping binder kind mismatch"
        (PS_Tm _, _) ->
          Left "morphism: type mapping binder kind mismatch"

    ensureFreshName tyAcc tmAcc name =
      let tyNames = map tvName tyAcc
          tmNames = map tmvName tmAcc
      in if name `elem` tyNames || name `elem` tmNames
          then Left "morphism: duplicate type mapping binders"
          else Right ()

    lookupMappedMode srcMode =
      case M.lookup srcMode modeMap of
        Nothing -> Left "morphism: missing mode mapping"
        Just tgtMode -> Right tgtMode

elabContext :: Doctrine -> ModeName -> [TyVar] -> [TmVar] -> M.Map Text (Int, TypeExpr) -> RawPolyContext -> Either Text Context
elabContext doc expectedMode tyVars tmVars tmBound ctx = do
  tys <- mapM (elabTypeExpr doc tyVars tmVars tmBound) ctx
  let bad = filter (\ty -> typeMode ty /= expectedMode) tys
  if null bad
    then Right tys
    else Left "boundary type must match generator mode"

elabTypeExpr :: Doctrine -> [TyVar] -> [TmVar] -> M.Map Text (Int, TypeExpr) -> RawPolyTypeExpr -> Either Text TypeExpr
elabTypeExpr doc tyVars tmVars tmBound expr =
  case expr of
    RPTVar name -> do
      case [v | v <- tyVars, tvName v == name] of
        [v] -> Right (TVar v)
        (_:_:_) -> Left ("duplicate type variable name: " <> name)
        [] -> do
          ref <- resolveTypeRef doc RawTypeRef { rtrMode = Nothing, rtrName = name }
          sig <- lookupTypeSig doc ref
          if null (tsParams sig)
            then Right (TCon ref [])
            else Left "type constructor arity mismatch"
    RPTMod rawMe innerRaw -> do
      me <- elabRawModExpr (dModes doc) rawMe
      inner <- elabTypeExpr doc tyVars tmVars tmBound innerRaw
      if typeMode inner /= meSrc me
        then Left "modality application source/argument mode mismatch"
        else normalizeTypeExpr (dModes doc) (TMod me inner)
    RPTCon rawRef args -> do
      case asModalityCall rawRef args of
        Just (rawMe, innerRaw) -> do
          me <- elabRawModExpr (dModes doc) rawMe
          inner <- elabTypeExpr doc tyVars tmVars tmBound innerRaw
          if typeMode inner /= meSrc me
            then Left "modality application source/argument mode mismatch"
            else normalizeTypeExpr (dModes doc) (TMod me inner)
        Nothing -> do
          ref <- resolveTypeRef doc rawRef
          sig <- lookupTypeSig doc ref
          let params = tsParams sig
          if length params /= length args
            then Left "type constructor arity mismatch"
            else do
              args' <- mapM (elabOneArg params) (zip params args)
              Right (TCon ref args')
  where
    elabOneArg _ (PS_Ty m, rawArg) = do
      argTy <- elabTypeExpr doc tyVars tmVars tmBound rawArg
      if typeMode argTy == m
        then Right (TAType argTy)
        else Left "type constructor argument mode mismatch"
    elabOneArg _ (PS_Tm sortTy, rawArg) = do
      tmArg <- elabTmTerm doc tyVars tmVars tmBound (Just sortTy) rawArg
      Right (TATm tmArg)

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
      let mode = ModeName modeTok
          tyName = TypeName tyTok
       in case M.lookup mode (dTypes doc) of
            Nothing -> False
            Just table -> M.member tyName table

elabTmTerm
  :: Doctrine
  -> [TyVar]
  -> [TmVar]
  -> M.Map Text (Int, TypeExpr)
  -> Maybe TypeExpr
  -> RawPolyTypeExpr
  -> Either Text TermDiagram
elabTmTerm doc _tyVars tmVars tmBound mExpected raw =
  do
    (expr, inferredSort) <- elabExpr mExpected raw
    let expectedSort = maybe inferredSort id mExpected
    tmCtx <- mkTmCtx
    termExprToDiagram ttDoc tmCtx expectedSort expr
  where
    ttDoc = doctrineTypeTheory doc

    elabExpr mExp tmRaw =
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
                      (funName, sig) <- lookupTmFunAny doc name 0
                      pure (TMFun funName [], tfsRes sig)
                    Just expected -> do
                      (funName, sig) <- lookupTmFunByName doc expected name 0
                      pure (TMFun funName [], tfsRes sig)
        RPTCon rawRef args ->
          case rtrMode rawRef of
            Just _ -> Left "term function names must be unqualified"
            Nothing -> do
              (funName, sig) <-
                case mExp of
                  Just expected -> lookupTmFunByName doc expected (rtrName rawRef) (length args)
                  Nothing -> lookupTmFunAny doc (rtrName rawRef) (length args)
              argExprs <- mapM (\(argSort, argRaw) -> fst <$> elabExpr (Just argSort) argRaw) (zip (tfsArgs sig) args)
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

lookupTmFunByName :: Doctrine -> TypeExpr -> Text -> Int -> Either Text (TmFunName, TmFunSig)
lookupTmFunByName doc expectedSort name arity = do
  let fname = TmFunName name
  let sigs = gatherCandidates (typeMode expectedSort)
  case sigs of
    [] -> Left ("unknown term function: " <> name)
    [sig] ->
      if length (tfsArgs sig) == arity
        then Right (fname, sig)
        else Left "term function arity mismatch"
    _ -> Left ("ambiguous term function in mode: " <> name)
  where
    gatherCandidates mode =
      let fromGens =
            [ TmFunSig
                { tfsArgs = [ ty | InPort ty <- gdDom gd ]
                , tfsRes = res
                }
            | gd <- maybe [] M.elems (M.lookup mode (dGens doc))
            , gdName gd == GenName name
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

lookupTmFunAny :: Doctrine -> Text -> Int -> Either Text (TmFunName, TmFunSig)
lookupTmFunAny doc name arity =
  case
    genCandidates
    of
      [] -> Left ("unknown term function: " <> name)
      [single] -> Right single
      _ -> Left ("ambiguous term function: " <> name)
  where
    genCandidates =
      [ ( TmFunName name
        , TmFunSig
            { tfsArgs = [ ty | InPort ty <- gdDom gd ]
            , tfsRes = res
            }
        )
      | modeTable <- M.elems (dGens doc)
      , gd <- M.elems modeTable
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

elabInputShapes :: Doctrine -> ModeName -> [TyVar] -> [TmVar] -> [RawInputShape] -> Either Text [InputShape]
elabInputShapes doc mode tyVars tmVars = mapM (elabInputShape doc mode tyVars tmVars)

elabInputShape :: Doctrine -> ModeName -> [TyVar] -> [TmVar] -> RawInputShape -> Either Text InputShape
elabInputShape doc mode tyVars tmVars shape =
  case shape of
    RIPort rawTy -> InPort <$> elabTypeExpr doc tyVars tmVars M.empty rawTy
    RIBinder binders rawCod -> do
      boundTys <- mapM (\b -> elabTypeExpr doc tyVars tmVars M.empty (rbvType b)) binders
      let binderPairs = zip binders boundTys
      let tmBinders = [ (rbvName b, ty) | (b, ty) <- binderPairs, typeMode ty /= mode ]
      let termBinders = [ b | (b, ty) <- binderPairs, typeMode ty == mode ]
      let tmCtx = map snd tmBinders
      let tmBound = M.fromList (zipWith (\(nm, ty) idx -> (nm, (idx, ty))) tmBinders [0..])
      bsDom <- mapM (\b -> elabTypeExpr doc tyVars tmVars tmBound (rbvType b)) termBinders
      bsCod <- elabContext doc mode tyVars tmVars tmBound rawCod
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
  -> [TyVar]
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
  -> [TyVar]
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

elabDiagExpr :: ModuleEnv -> Doctrine -> ModeName -> [TyVar] -> RawDiagExpr -> Either Text Diagram
elabDiagExpr env doc mode ruleVars expr = do
  (diag, _) <- elabDiagExprWith env doc mode [] ruleVars [] M.empty BMNoMeta False expr
  ensureAttrVarNameSortsDiagram (freeAttrVarsDiagram diag)
  ensureAcyclicMode doc mode diag
  pure diag

elabDiagExprWith
  :: ModuleEnv
  -> Doctrine
  -> ModeName
  -> [TypeExpr]
  -> [TyVar]
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
  -> [TypeExpr]
  -> [TyVar]
  -> [TmVar]
  -> M.Map BinderMetaVar BinderSig
  -> BinderMetaMode
  -> Bool
  -> RawDiagExpr
  -> Fresh (Diagram, M.Map BinderMetaVar BinderSig)
elabDiagExprWithFresh env doc mode tmCtx tyVars tmVars binderSigs0 metaMode allowSplice expr =
  build tmCtx binderSigs0 expr
  where
    rigidTy = S.fromList tyVars
    rigidTm = S.fromList tmVars
    ttDoc = doctrineTypeTheory doc

    build curTmCtx binderSigs e =
      case e of
        RDId ctx -> do
          ctx' <- liftEither (elabContext doc mode tyVars tmVars M.empty ctx)
          pure (idDTm mode curTmCtx ctx', binderSigs)
        RDMetaVar name -> do
          (_, ty) <- freshTyVar TyVar { tvName = "mv_" <> name, tvMode = mode }
          let (pid, d0) = freshPort ty (emptyDiagram mode curTmCtx)
          d1 <- liftEither (setPortLabel pid name d0)
          pure (d1 { dIn = [pid], dOut = [pid] }, binderSigs)
        RDGen name mArgs mAttrArgs mBinderArgs -> do
          gen <- liftEither (lookupGen doc mode (GenName name))
          tyRename <- freshTySubst (gdTyVars gen)
          tmRename <- freshTmSubst ttDoc curTmCtx (gdTmVars gen)
          let renameSubst = U.Subst { U.sTy = tyRename, U.sTm = tmRename }
          dom0 <- applySubstCtxDoc renameSubst (gdPlainDom gen)
          cod0 <- applySubstCtxDoc renameSubst (gdCod gen)
          binderSlots0 <- mapM (applySubstBinderSig renameSubst) [ bs | InBinder bs <- gdDom gen ]
          (dom, cod, binderSlots) <-
            case mArgs of
              Nothing -> pure (dom0, cod0, binderSlots0)
              Just args -> do
                let tyArity = length (gdTyVars gen)
                let tmArity = length (gdTmVars gen)
                if length args /= tyArity + tmArity
                  then liftEither (Left "generator type/term argument mismatch")
                  else do
                    let (tyRawArgs, tmRawArgs) = splitAt tyArity args
                    tyArgs <- mapM (liftEither . elabTypeExpr doc tyVars tmVars M.empty) tyRawArgs
                    freshTyVars <- liftEither (extractFreshTyVars (gdTyVars gen) tyRename)
                    case and (zipWith (\v t -> tvMode v == typeMode t) freshTyVars tyArgs) of
                      False -> liftEither (Left "generator type argument mode mismatch")
                      True -> pure ()
                    freshTmVars <- liftEither (extractFreshTmVars (gdTmVars gen) tmRename)
                    tmArgs <- mapM (uncurry (elabTmArg curTmCtx)) (zip freshTmVars tmRawArgs)
                    let argSubst =
                          U.Subst
                            { U.sTy = M.fromList (zip freshTyVars tyArgs)
                            , U.sTm = M.fromList (zip freshTmVars tmArgs)
                            }
                    dom1 <- applySubstCtxDoc argSubst dom0
                    cod1 <- applySubstCtxDoc argSubst cod0
                    binderSlots1 <- mapM (applySubstBinderSig argSubst) binderSlots0
                    pure (dom1, cod1, binderSlots1)
          attrs <- liftEither (elabGenAttrs doc gen mAttrArgs)
          (binderArgs, binderSigs') <- elaborateBinderArgs binderSigs binderSlots mBinderArgs
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
          (inner, binderSigs') <- build curTmCtx binderSigs innerExpr
          dom <- liftEither (diagramDom inner)
          cod <- liftEither (diagramCod inner)
          let (ins, diag0) = allocPorts dom (emptyDiagram mode curTmCtx)
          let (outs, diag1) = allocPorts cod diag0
          diag2 <- liftEither (addEdgePayload (PBox (BoxName name) inner) ins outs diag1)
          let diag3 = diag2 { dIn = ins, dOut = outs }
          liftEither (validateDiagram diag3)
          pure (diag3, binderSigs')
        RDLoop innerExpr -> do
          (inner, binderSigs') <- build curTmCtx binderSigs innerExpr
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
          (d1, binderSigs1) <- build curTmCtx binderSigs a
          (d2, binderSigs2) <- build curTmCtx binderSigs1 b
          dComp <- liftEither (compD ttDoc d2 d1)
          pure (dComp, binderSigs2)
        RDTensor a b -> do
          (d1, binderSigs1) <- build curTmCtx binderSigs a
          (d2, binderSigs2) <- build curTmCtx binderSigs1 b
          dTen <- liftEither (tensorD d1 d2)
          pure (dTen, binderSigs2)

    elaborateBinderArgs binderSigs binderSlots mBinderArgs =
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
              domArg' <- canonicalCtx domArg
              codArg' <- canonicalCtx codArg
              slotDom' <- canonicalCtx (bsDom slot)
              slotCod' <- canonicalCtx (bsCod slot)
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

    elabTmArg curTmCtx v rawArg =
      case elabTmTerm doc tyVars tmVars M.empty (Just (tmvSort v)) rawArg of
        Right tm -> pure tm
        Left err ->
          case rawArg of
            RPTVar name ->
              case implicitBoundCandidate curTmCtx (tmvSort v) of
                Right (Just idx) ->
                  case termExprToDiagram ttDoc curTmCtx (tmvSort v) (TMBound idx) of
                    Right tm -> pure tm
                    Left msg -> liftEither (Left ("explicit term argument `" <> name <> "`: " <> msg))
                Right Nothing -> liftEither (Left err)
                Left msg -> liftEither (Left ("explicit term argument `" <> name <> "`: " <> msg))
            _ ->
              liftEither (Left err)
      where
        implicitBoundCandidate ctx expectedSort = do
          expectedNorm <- normalizeTypeDeep ttDoc expectedSort
          let candidates =
                [ (idx, sortTy)
                | (idx, sortTy) <- zip [0 :: Int ..] ctx
                , typeMode sortTy == typeMode expectedNorm
                ]
          matching <- fmap catMaybes $ mapM (matches expectedNorm) candidates
          case matching of
            [] -> Right Nothing
            [idx] -> Right (Just idx)
            _ -> Left "ambiguous bound term variable (multiple binder variables share this sort)"

        matches expectedNorm (idx, sortTy) = do
          sortNorm <- normalizeTypeDeep ttDoc sortTy
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
      case diagramPortType d pid of
        Nothing -> Left "loop: internal missing port type"
        Just ty -> Right ty

    canonicalCtx ctx = liftEither (mapM (U.applySubstTy ttDoc U.emptySubst) ctx)

    applySubstCtxDoc subst ctx = liftEither (U.applySubstCtx ttDoc subst ctx)

    applySubstBinderSig subst bs = do
      tmCtx' <- applySubstCtxDoc subst (bsTmCtx bs)
      dom' <- applySubstCtxDoc subst (bsDom bs)
      cod' <- applySubstCtxDoc subst (bsCod bs)
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

unifyBoundary :: TypeTheory -> S.Set TyVar -> S.Set TmVar -> Context -> Context -> Diagram -> Either Text Diagram
unifyBoundary tt rigidTy rigidTm dom cod diag = do
  domDiag <- diagramDom diag
  let flexTy0 = S.difference (freeTyVarsDiagram diag) rigidTy
  let flexTm0 = S.difference (freeTmVarsDiagram diag) rigidTm
  s1 <- U.unifyCtx tt (dTmCtx diag) flexTy0 flexTm0 domDiag dom
  diag1 <- applySubstDiagram tt s1 diag
  codDiag <- diagramCod diag1
  let flexTy1 = S.difference (freeTyVarsDiagram diag1) rigidTy
  let flexTm1 = S.difference (freeTmVarsDiagram diag1) rigidTm
  s2 <- U.unifyCtx tt (dTmCtx diag1) flexTy1 flexTm1 codDiag cod
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

freshTySubst :: [TyVar] -> Fresh (M.Map TyVar TypeExpr)
freshTySubst vars = do
  pairs <- mapM freshTyVar vars
  pure (M.fromList pairs)

freshTmSubst :: TypeTheory -> [TypeExpr] -> [TmVar] -> Fresh (M.Map TmVar TermDiagram)
freshTmSubst ttDoc tmCtx vars = do
  pairs <- mapM (freshTmVar ttDoc tmCtx) vars
  pure (M.fromList pairs)

extractFreshTyVars :: [TyVar] -> M.Map TyVar TypeExpr -> Either Text [TyVar]
extractFreshTyVars vars subst =
  mapM lookupVar vars
  where
    lookupVar v =
      case M.lookup v subst of
        Just (TVar v') -> Right v'
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

freshTyVar :: TyVar -> Fresh (TyVar, TypeExpr)
freshTyVar v = do
  n <- freshInt
  let name = tvName v <> T.pack ("#" <> show n)
  let fresh = TyVar { tvName = name, tvMode = tvMode v }
  pure (v, TVar fresh)

freshTmVar :: TypeTheory -> [TypeExpr] -> TmVar -> Fresh (TmVar, TermDiagram)
freshTmVar ttDoc tmCtx v = do
  n <- freshInt
  let name = tmvName v <> T.pack ("#" <> show n)
  let fresh = TmVar { tmvName = name, tmvSort = tmvSort v, tmvScope = max (tmvScope v) (length tmCtx) }
  tm <- liftEither (termExprToDiagram ttDoc tmCtx (tmvSort fresh) (TMVar fresh))
  pure (v, tm)

freshInt :: Fresh Int
freshInt = Fresh (\n -> Right (n, n + 1))

liftEither :: Either Text a -> Fresh a
liftEither (Left err) = Fresh (\_ -> Left err)
liftEither (Right a) = pure a
