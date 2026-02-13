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
import Control.Monad (foldM, when)
import Strat.DSL.AST (RawPolyMorphism(..), RawPolyMorphismItem(..), RawPolyTypeMap(..), RawPolyGenMap(..), RawPolyModeMap(..), RawPolyModalityMap(..), RawPolyAttrSortMap(..))
import Strat.Poly.DSL.AST
import Strat.Poly.Doctrine
import Strat.Poly.Diagram
import Strat.Poly.Graph (emptyDiagram, freshPort, setPortLabel, addEdgePayload, Edge(..), EdgeId(..), PortId(..), EdgePayload(..), BinderArg(..), BinderMetaVar(..), validateDiagram, diagramPortType)
import Strat.Poly.ModeTheory
import Strat.Poly.Names
import Strat.Poly.TypeExpr
import Strat.Poly.IndexTheory (IxTheory(..), IxFunSig(..), IxRule(..))
import qualified Strat.Poly.UnifyTy as U
import Strat.Poly.TypeTheory (TypeTheory)
import Strat.Poly.Attr
import Strat.Poly.Morphism
import Strat.Frontend.Env (ModuleEnv(..), TermDef(..))
import Strat.Frontend.Coerce (coerceDiagramTo)
import Strat.Poly.Cell2 (Cell2(..))
import Strat.Common.Rules (RewritePolicy(..))

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
  let ixFunMap = M.empty
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
        , morIxFunMap = ixFunMap
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
        , morIxFunMap = ixFunMap
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
    mapIxVarSort mor v = do
      sort' <- applyMorphismTy mor (ixvSort v)
      pure v { ixvSort = sort' }
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
      (tmplParams, tyVarsTgt, ixVarsTgt) <- buildTypeTemplateParams tgt modeMap (tsParams sig) (rpmtParams decl)
      tgtExpr <- elabTypeExpr tgt tyVarsTgt ixVarsTgt M.empty (rpmtTgtType decl)
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
      ixVarsTgt <- mapM (mapIxVarSort mor0) (gdIxVars gen)
      binderSigs0 <- buildBinderHoleSigs mor0 gen
      (diag0, _) <- elabDiagExprWith env tgt modeTgt [] tyVarsTgt ixVarsTgt binderSigs0 BMUse True (rpmgRhs decl)
      let domSrc = gdPlainDom gen
      let codSrc = gdCod gen
      domTgt <- mapM (applyMorphismTy mor0) domSrc
      codTgt <- mapM (applyMorphismTy mor0) codSrc
      let rigidTy = S.fromList tyVarsTgt
      let rigidIx = S.fromList ixVarsTgt
      let ttTgt = doctrineTypeTheory tgt
      diag <- unifyBoundary ttTgt rigidTy rigidIx domTgt codTgt diag0
      let freeTy = freeTyVarsDiagram diag
      let allowedTy = S.fromList tyVarsTgt
      if S.isSubsetOf freeTy allowedTy
        then Right ()
        else Left "morphism: generator mapping uses undeclared type variables"
      let freeIx = freeIxVarsDiagram diag
      let allowedIx = S.fromList ixVarsTgt
      if S.isSubsetOf freeIx allowedIx
        then Right ()
        else Left "morphism: generator mapping uses undeclared index variables"
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
      ixCtx' <- mapM (applyMorphismTy mor) (bsIxCtx sig)
      dom' <- mapM (applyMorphismTy mor) (bsDom sig)
      cod' <- mapM (applyMorphismTy mor) (bsCod sig)
      pure (hole, sig { bsIxCtx = ixCtx', bsDom = dom', bsCod = cod' })
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
  pure doc

seedDoctrine :: Text -> Maybe Doctrine -> Doctrine
seedDoctrine name base =
  case base of
    Nothing -> Doctrine
      { dName = name
      , dModes = emptyModeTheory
      , dAcyclicModes = S.empty
      , dIndexModes = S.empty
      , dIxTheory = M.empty
      , dAttrSorts = M.empty
      , dTypes = M.empty
      , dGens = M.empty
      , dCells2 = []
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
    RPIndexMode name -> do
      let mode = ModeName name
      ensureMode doc mode
      let ixTheory' =
            M.insertWith
              (\_ old -> old)
              mode
              (IxTheory M.empty [])
              (dIxTheory doc)
      pure doc { dIndexModes = S.insert mode (dIndexModes doc), dIxTheory = ixTheory' }
    RPIndexFun decl -> do
      let mode = ModeName (rifMode decl)
      ensureMode doc mode
      vars <- mapM (elabIxDeclVar doc []) (rifArgs decl)
      argSorts <- mapM (pure . ixvSort) vars
      resSort <- elabTypeExpr doc [] [] M.empty (rifRes decl)
      let sig = IxFunSig { ifArgs = argSorts, ifRes = resSort }
      let table0 = M.findWithDefault (IxTheory M.empty []) mode (dIxTheory doc)
      let funs0 = itFuns table0
      if M.member (IxFunName (rifName decl)) funs0
        then Left "duplicate index_fun name"
        else do
          let table1 = table0 { itFuns = M.insert (IxFunName (rifName decl)) sig funs0 }
          pure doc { dIxTheory = M.insert mode table1 (dIxTheory doc) }
    RPIndexRule decl -> do
      let mode = ModeName (rirMode decl)
      ensureMode doc mode
      vars <- mapM (elabIxDeclVar doc []) (rirVars decl)
      lhs <- elabIxTerm doc [] vars M.empty Nothing (rirLHS decl)
      rhs <- elabIxTerm doc [] vars M.empty Nothing (rirRHS decl)
      let rule = IxRule { irVars = vars, irLHS = lhs, irRHS = rhs }
      let table0 = M.findWithDefault (IxTheory M.empty []) mode (dIxTheory doc)
      let table1 = table0 { itRules = itRules table0 <> [rule] }
      pure doc { dIxTheory = M.insert mode table1 (dIxTheory doc) }
    RPStructure decl -> do
      let mode = ModeName (rsMode decl)
      mt' <- setModeDiscipline mode (rsDisc decl) (dModes doc)
      pure doc { dModes = mt' }
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
    RPAdjunction decl -> do
      let left = ModName (raLeft decl)
      let right = ModName (raRight decl)
      mt' <- addAdjDecl (AdjDecl left right) (dModes doc)
      addAdjGens (doc { dModes = mt' }) left right
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
      (tyVars, ixVars, _sigParams) <- elabParamDecls doc mode (rpgVars decl)
      attrs <- mapM (resolveAttrField doc) (rpgAttrs decl)
      ensureDistinct "duplicate generator attribute field name" (map fst attrs)
      dom <- elabInputShapes doc mode tyVars ixVars (rpgDom decl)
      cod <- elabContext doc mode tyVars ixVars M.empty (rpgCod decl)
      let gen = GenDecl
            { gdName = gname
            , gdMode = mode
            , gdTyVars = tyVars
            , gdIxVars = ixVars
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
      (ruleTyVars, ruleIxVars, _sigParams) <- elabParamDecls doc mode (rprVars decl)
      dom <- elabContext doc mode ruleTyVars ruleIxVars M.empty (rprDom decl)
      cod <- elabContext doc mode ruleTyVars ruleIxVars M.empty (rprCod decl)
      (lhs, binderSigs) <- withRule (elabRuleLHS env doc mode ruleTyVars ruleIxVars (rprLHS decl))
      rhs <- withRule (elabRuleRHS env doc mode ruleTyVars ruleIxVars binderSigs (rprRHS decl))
      let rigidTy = S.fromList ruleTyVars
      let rigidIx = S.fromList ruleIxVars
      let tt = doctrineTypeTheory doc
      lhs' <- unifyBoundary tt rigidTy rigidIx dom cod lhs
      rhs' <- unifyBoundary tt rigidTy rigidIx dom cod rhs
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
            , c2IxVars = ruleIxVars
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

addAdjGens :: Doctrine -> ModName -> ModName -> Either Text Doctrine
addAdjGens doc left right = do
  leftDecl <- requireDecl left
  rightDecl <- requireDecl right
  if mdSrc leftDecl /= mdTgt rightDecl || mdTgt leftDecl /= mdSrc rightDecl
    then Left "adjunction modalities must have opposite directions"
    else Right ()
  let modeM = mdSrc leftDecl
  let modeN = mdTgt leftDecl
  let aVar = TyVar { tvName = "a", tvMode = modeM }
  let bVar = TyVar { tvName = "b", tvMode = modeN }
  let fExpr = ModExpr { meSrc = modeM, meTgt = modeN, mePath = [left] }
  let uExpr = ModExpr { meSrc = modeN, meTgt = modeM, mePath = [right] }
  let unitName = GenName ("unit_" <> renderModName left)
  let counitName = GenName ("counit_" <> renderModName left)
  unitCod <- normalizeTypeExpr mt (TMod uExpr (TMod fExpr (TVar aVar)))
  counitDom <- normalizeTypeExpr mt (TMod fExpr (TMod uExpr (TVar bVar)))
  let unitGen =
        GenDecl
          { gdName = unitName
          , gdMode = modeM
          , gdTyVars = [aVar]
          , gdIxVars = []
          , gdDom = [InPort (TVar aVar)]
          , gdCod = [unitCod]
          , gdAttrs = []
          }
  let counitGen =
        GenDecl
          { gdName = counitName
          , gdMode = modeN
          , gdTyVars = [bVar]
          , gdIxVars = []
          , gdDom = [InPort counitDom]
          , gdCod = [TVar bVar]
          , gdAttrs = []
          }
  gens1 <- insertGen modeM unitGen (dGens doc)
  gens2 <- insertGen modeN counitGen gens1
  pure doc { dGens = gens2 }
  where
    mt = dModes doc
    requireDecl name =
      case M.lookup name (mtDecls mt) of
        Nothing -> Left ("unknown modality: " <> renderModName name)
        Just decl -> Right decl

    renderModName (ModName n) = n

    insertGen mode gen gens =
      let table = M.findWithDefault M.empty mode gens
       in if M.member (gdName gen) table
            then Left ("adjunction-generated generator already exists: " <> renderGenName (gdName gen))
            else Right (M.insert mode (M.insert (gdName gen) gen table) gens)

    renderGenName (GenName n) = n

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

elabIxDeclVar :: Doctrine -> [TyVar] -> RawIxVarDecl -> Either Text IxVar
elabIxDeclVar doc tyVars decl = do
  sortTy <- elabTypeExpr doc tyVars [] M.empty (rivSort decl)
  pure IxVar { ixvName = rivName decl, ixvSort = sortTy, ixvScope = 0 }

elabParamDecls :: Doctrine -> ModeName -> [RawParamDecl] -> Either Text ([TyVar], [IxVar], [ParamSig])
elabParamDecls doc defaultMode params = go [] [] [] params
  where
    go tyAcc ixAcc sigAcc [] = Right (reverse tyAcc, reverse ixAcc, reverse sigAcc)
    go tyAcc ixAcc sigAcc (p:rest) =
      case p of
        RPDType tvDecl -> do
          tv <- resolveTyVarDecl doc defaultMode tvDecl
          let name = tvName tv
          if name `elem` map tvName tyAcc || name `elem` map ixvName ixAcc
            then Left "duplicate parameter name"
            else go (tv:tyAcc) ixAcc (PS_Ty (tvMode tv) : sigAcc) rest
        RPDIndex ixDecl -> do
          let name = rivName ixDecl
          if name `elem` map tvName tyAcc || name `elem` map ixvName ixAcc
            then Left "duplicate parameter name"
            else do
              ixVar <- elabIxDeclVar doc tyAcc ixDecl
              go tyAcc (ixVar:ixAcc) (PS_Ix (ixvSort ixVar) : sigAcc) rest

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
  -> Either Text ([TemplateParam], [TyVar], [IxVar])
buildTypeTemplateParams tgt modeMap sigParams decls = do
  if length sigParams /= length decls
    then Left "morphism: type mapping binder arity mismatch"
    else go [] [] [] (zip sigParams decls)
  where
    go tyAcc ixAcc tmplAcc [] =
      Right (reverse tmplAcc, reverse tyAcc, reverse ixAcc)
    go tyAcc ixAcc tmplAcc ((sigParam, decl):rest) =
      case (sigParam, decl) of
        (PS_Ty srcMode, RPDType tyDecl) -> do
          expectedMode <- lookupMappedMode srcMode
          tyVar <- resolveTyVarDecl tgt expectedMode tyDecl
          ensureFreshName tyAcc ixAcc (tvName tyVar)
          go (tyVar:tyAcc) ixAcc (TPType tyVar:tmplAcc) rest
        (PS_Ix srcSort, RPDIndex ixDecl) -> do
          expectedMode <- lookupMappedMode (typeMode srcSort)
          ixSort <- elabTypeExpr tgt (reverse tyAcc) (reverse ixAcc) M.empty (rivSort ixDecl)
          if typeMode ixSort /= expectedMode
            then Left "morphism: type mapping index binder mode mismatch"
            else Right ()
          if expectedMode `S.member` dIndexModes tgt
            then Right ()
            else Left "morphism: type mapping index binder must live in an index mode"
          ensureFreshName tyAcc ixAcc (rivName ixDecl)
          let ixVar = IxVar { ixvName = rivName ixDecl, ixvSort = ixSort, ixvScope = 0 }
          go tyAcc (ixVar:ixAcc) (TPIx ixVar:tmplAcc) rest
        (PS_Ty _, _) ->
          Left "morphism: type mapping binder kind mismatch"
        (PS_Ix _, _) ->
          Left "morphism: type mapping binder kind mismatch"

    ensureFreshName tyAcc ixAcc name =
      let tyNames = map tvName tyAcc
          ixNames = map ixvName ixAcc
      in if name `elem` tyNames || name `elem` ixNames
          then Left "morphism: duplicate type mapping binders"
          else Right ()

    lookupMappedMode srcMode =
      case M.lookup srcMode modeMap of
        Nothing -> Left "morphism: missing mode mapping"
        Just tgtMode -> Right tgtMode

elabContext :: Doctrine -> ModeName -> [TyVar] -> [IxVar] -> M.Map Text (Int, TypeExpr) -> RawPolyContext -> Either Text Context
elabContext doc expectedMode tyVars ixVars ixBound ctx = do
  tys <- mapM (elabTypeExpr doc tyVars ixVars ixBound) ctx
  let bad = filter (\ty -> typeMode ty /= expectedMode) tys
  if null bad
    then Right tys
    else Left "boundary type must match generator mode"

elabTypeExpr :: Doctrine -> [TyVar] -> [IxVar] -> M.Map Text (Int, TypeExpr) -> RawPolyTypeExpr -> Either Text TypeExpr
elabTypeExpr doc tyVars ixVars ixBound expr =
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
    RPTBound _ ->
      Left "bound index variable (^i) is only valid in index argument positions"
    RPTMod rawMe innerRaw -> do
      me <- elabRawModExpr (dModes doc) rawMe
      inner <- elabTypeExpr doc tyVars ixVars ixBound innerRaw
      if typeMode inner /= meSrc me
        then Left "modality application source/argument mode mismatch"
        else normalizeTypeExpr (dModes doc) (TMod me inner)
    RPTCon rawRef args -> do
      case asModalityCall rawRef args of
        Just (rawMe, innerRaw) -> do
          me <- elabRawModExpr (dModes doc) rawMe
          inner <- elabTypeExpr doc tyVars ixVars ixBound innerRaw
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
      argTy <- elabTypeExpr doc tyVars ixVars ixBound rawArg
      if typeMode argTy == m
        then Right (TAType argTy)
        else Left "type constructor argument mode mismatch"
    elabOneArg _ (PS_Ix sortTy, rawArg) = do
      ix <- elabIxTerm doc tyVars ixVars ixBound (Just sortTy) rawArg
      Right (TAIndex ix)

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

elabIxTerm
  :: Doctrine
  -> [TyVar]
  -> [IxVar]
  -> M.Map Text (Int, TypeExpr)
  -> Maybe TypeExpr
  -> RawPolyTypeExpr
  -> Either Text IxTerm
elabIxTerm doc tyVars ixVars ixBound mExpected raw =
  case raw of
    RPTBound i -> Right (IXBound i)
    RPTMod _ _ -> Left "index terms do not support modality application"
    RPTVar name ->
      case M.lookup name ixBound of
        Just (idx, _) -> Right (IXBound idx)
        Nothing ->
          case [v | v <- ixVars, ixvName v == name] of
            [v] -> Right (IXVar v)
            (_:_:_) -> Left ("duplicate index variable name: " <> name)
            [] ->
              case mExpected of
                Nothing -> do
                  (funName, _sig) <- lookupIxFunAny doc name 0
                  pure (IXFun funName [])
                Just expected -> do
                  (funName, _sig) <- lookupIxFunByName doc expected name 0
                  pure (IXFun funName [])
    RPTCon rawRef args -> do
      case rtrMode rawRef of
        Just _ -> Left "index function names must be unqualified"
        Nothing -> do
          (funName, sig) <-
            case mExpected of
              Just expected -> lookupIxFunByName doc expected (rtrName rawRef) (length args)
              Nothing -> lookupIxFunAny doc (rtrName rawRef) (length args)
          ixArgs <- mapM (uncurry (elabIxTerm doc tyVars ixVars ixBound . Just)) (zip (ifArgs sig) args)
          pure (IXFun funName ixArgs)

lookupIxFunByName :: Doctrine -> TypeExpr -> Text -> Int -> Either Text (IxFunName, IxFunSig)
lookupIxFunByName doc expectedSort name arity = do
  theory <-
    case M.lookup (typeMode expectedSort) (dIxTheory doc) of
      Nothing -> Left "missing index theory for expected index sort"
      Just th -> Right th
  let fname = IxFunName name
  sig <-
    case M.lookup fname (itFuns theory) of
      Nothing -> Left ("unknown index function: " <> name)
      Just s -> Right s
  if length (ifArgs sig) /= arity
    then Left "index function arity mismatch"
    else Right (fname, sig)

lookupIxFunAny :: Doctrine -> Text -> Int -> Either Text (IxFunName, IxFunSig)
lookupIxFunAny doc name arity =
  case
    [ (fname, sig)
    | theory <- M.elems (dIxTheory doc)
    , (fname@(IxFunName fnameTxt), sig) <- M.toList (itFuns theory)
    , fnameTxt == name
    , length (ifArgs sig) == arity
    ]
    of
      [] -> Left ("unknown index function: " <> name)
      [single] -> Right single
      _ -> Left ("ambiguous index function: " <> name)

elabInputShapes :: Doctrine -> ModeName -> [TyVar] -> [IxVar] -> [RawInputShape] -> Either Text [InputShape]
elabInputShapes doc mode tyVars ixVars = mapM (elabInputShape doc mode tyVars ixVars)

elabInputShape :: Doctrine -> ModeName -> [TyVar] -> [IxVar] -> RawInputShape -> Either Text InputShape
elabInputShape doc mode tyVars ixVars shape =
  case shape of
    RIPort rawTy -> InPort <$> elabTypeExpr doc tyVars ixVars M.empty rawTy
    RIBinder binders rawCod -> do
      boundTys <- mapM (\b -> elabTypeExpr doc tyVars ixVars M.empty (rbvType b)) binders
      let binderPairs = zip binders boundTys
      let ixBinders = [ (rbvName b, ty) | (b, ty) <- binderPairs, typeMode ty `S.member` dIndexModes doc ]
      let termBinders = [ b | (b, ty) <- binderPairs, typeMode ty == mode ]
      let badBinders = [ b | (b, ty) <- binderPairs, typeMode ty /= mode && typeMode ty `S.notMember` dIndexModes doc ]
      if null badBinders
        then Right ()
        else Left "binder variable mode must be either generator mode or index mode"
      let ixCtx = map snd ixBinders
      let ixBound = M.fromList (zipWith (\(nm, ty) idx -> (nm, (idx, ty))) ixBinders [0..])
      bsDom <- mapM (\b -> elabTypeExpr doc tyVars ixVars ixBound (rbvType b)) termBinders
      bsCod <- elabContext doc mode tyVars ixVars ixBound rawCod
      pure (InBinder BinderSig { bsIxCtx = ixCtx, bsDom = bsDom, bsCod = bsCod })

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
  -> [IxVar]
  -> RawDiagExpr
  -> Either Text (Diagram, M.Map BinderMetaVar BinderSig)
elabRuleLHS env doc mode tyVars ixVars expr = do
  (diag, metas) <- elabDiagExprWith env doc mode [] tyVars ixVars M.empty BMCollect False expr
  ensureAttrVarNameSortsDiagram (freeAttrVarsDiagram diag)
  ensureAcyclicMode doc mode diag
  pure (diag, metas)

elabRuleRHS
  :: ModuleEnv
  -> Doctrine
  -> ModeName
  -> [TyVar]
  -> [IxVar]
  -> M.Map BinderMetaVar BinderSig
  -> RawDiagExpr
  -> Either Text Diagram
elabRuleRHS env doc mode tyVars ixVars binderSigs expr = do
  (diag, metas) <- elabDiagExprWith env doc mode [] tyVars ixVars binderSigs BMUse True expr
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
  -> [IxVar]
  -> M.Map BinderMetaVar BinderSig
  -> BinderMetaMode
  -> Bool
  -> RawDiagExpr
  -> Either Text (Diagram, M.Map BinderMetaVar BinderSig)
elabDiagExprWith env doc mode ixCtx tyVars ixVars binderSigs0 metaMode allowSplice expr =
  ensureLinearMetaVars expr *> evalFresh (elabDiagExprWithFresh env doc mode ixCtx tyVars ixVars binderSigs0 metaMode allowSplice expr)

elabDiagExprWithFresh
  :: ModuleEnv
  -> Doctrine
  -> ModeName
  -> [TypeExpr]
  -> [TyVar]
  -> [IxVar]
  -> M.Map BinderMetaVar BinderSig
  -> BinderMetaMode
  -> Bool
  -> RawDiagExpr
  -> Fresh (Diagram, M.Map BinderMetaVar BinderSig)
elabDiagExprWithFresh env doc mode ixCtx tyVars ixVars binderSigs0 metaMode allowSplice expr =
  build ixCtx binderSigs0 expr
  where
    rigidTy = S.fromList tyVars
    rigidIx = S.fromList ixVars
    ttDoc = doctrineTypeTheory doc

    build curIxCtx binderSigs e =
      case e of
        RDId ctx -> do
          ctx' <- liftEither (elabContext doc mode tyVars ixVars M.empty ctx)
          pure (idDIx mode curIxCtx ctx', binderSigs)
        RDMetaVar name -> do
          (_, ty) <- freshTyVar TyVar { tvName = "mv_" <> name, tvMode = mode }
          let (pid, d0) = freshPort ty (emptyDiagram mode curIxCtx)
          d1 <- liftEither (setPortLabel pid name d0)
          pure (d1 { dIn = [pid], dOut = [pid] }, binderSigs)
        RDGen name mArgs mAttrArgs mBinderArgs -> do
          gen <- liftEither (lookupGen doc mode (GenName name))
          tyRename <- freshTySubst (gdTyVars gen)
          ixRename <- freshIxSubst (length curIxCtx) (gdIxVars gen)
          let renameSubst = U.Subst { U.sTy = tyRename, U.sIx = ixRename }
          dom0 <- applySubstCtxDoc renameSubst (gdPlainDom gen)
          cod0 <- applySubstCtxDoc renameSubst (gdCod gen)
          binderSlots0 <- mapM (applySubstBinderSig renameSubst) [ bs | InBinder bs <- gdDom gen ]
          (dom, cod, binderSlots) <-
            case mArgs of
              Nothing -> pure (dom0, cod0, binderSlots0)
              Just args -> do
                let tyArity = length (gdTyVars gen)
                let ixArity = length (gdIxVars gen)
                if length args /= tyArity + ixArity
                  then liftEither (Left "generator type/index argument mismatch")
                  else do
                    let (tyRawArgs, ixRawArgs) = splitAt tyArity args
                    tyArgs <- mapM (liftEither . elabTypeExpr doc tyVars ixVars M.empty) tyRawArgs
                    freshTyVars <- liftEither (extractFreshTyVars (gdTyVars gen) tyRename)
                    case and (zipWith (\v t -> tvMode v == typeMode t) freshTyVars tyArgs) of
                      False -> liftEither (Left "generator type argument mode mismatch")
                      True -> pure ()
                    freshIxVars <- liftEither (extractFreshIxVars (gdIxVars gen) ixRename)
                    ixArgs <- mapM (uncurry elabIxArg) (zip freshIxVars ixRawArgs)
                    let argSubst =
                          U.Subst
                            { U.sTy = M.fromList (zip freshTyVars tyArgs)
                            , U.sIx = M.fromList (zip freshIxVars ixArgs)
                            }
                    dom1 <- applySubstCtxDoc argSubst dom0
                    cod1 <- applySubstCtxDoc argSubst cod0
                    binderSlots1 <- mapM (applySubstBinderSig argSubst) binderSlots0
                    pure (dom1, cod1, binderSlots1)
          attrs <- liftEither (elabGenAttrs doc gen mAttrArgs)
          (binderArgs, binderSigs') <- elaborateBinderArgs curIxCtx binderSigs binderSlots mBinderArgs
          diag <- liftEither (mkGenDiag curIxCtx (gdName gen) attrs binderArgs dom cod)
          pure (diag, binderSigs')
        RDTermRef name -> do
          term <- liftEither (lookupTerm env name)
          if tdDoctrine term == dName doc
            then
              if tdMode term /= mode
                then liftEither (Left ("term @" <> name <> " has mode " <> renderModeName (tdMode term) <> ", expected " <> renderModeName mode))
                else
                  if dIxCtx (tdDiagram term) == curIxCtx
                    then pure (tdDiagram term, binderSigs)
                    else liftEither (Left ("term @" <> name <> " has incompatible index context"))
            else do
              srcDoc <- liftEither (lookupDoctrine env (tdDoctrine term))
              (doc', diag') <- liftEither (coerceDiagramTo env srcDoc (tdDiagram term) (dName doc))
              if dName doc' /= dName doc
                then liftEither (Left ("term @" <> name <> " has doctrine " <> tdDoctrine term <> ", expected " <> dName doc))
                else if dMode diag' /= mode
                  then liftEither (Left ("term @" <> name <> " has mode " <> renderModeName (dMode diag') <> ", expected " <> renderModeName mode))
                  else
                    if dIxCtx diag' == curIxCtx
                      then pure (diag', binderSigs)
                      else liftEither (Left ("term @" <> name <> " has incompatible index context"))
        RDSplice name ->
          if allowSplice
            then do
              let meta = BinderMetaVar name
              sig <- liftEither $
                case M.lookup meta binderSigs of
                  Nothing -> Left "splice references unknown binder meta"
                  Just bs -> Right bs
              diag <- liftEither (mkSpliceDiag curIxCtx meta (bsDom sig) (bsCod sig))
              pure (diag, binderSigs)
            else liftEither (Left "splice is only allowed in rule RHS")
        RDBox name innerExpr -> do
          (inner, binderSigs') <- build curIxCtx binderSigs innerExpr
          dom <- liftEither (diagramDom inner)
          cod <- liftEither (diagramCod inner)
          let (ins, diag0) = allocPorts dom (emptyDiagram mode curIxCtx)
          let (outs, diag1) = allocPorts cod diag0
          diag2 <- liftEither (addEdgePayload (PBox (BoxName name) inner) ins outs diag1)
          let diag3 = diag2 { dIn = ins, dOut = outs }
          liftEither (validateDiagram diag3)
          pure (diag3, binderSigs')
        RDLoop innerExpr -> do
          (inner, binderSigs') <- build curIxCtx binderSigs innerExpr
          case (dIn inner, dOut inner) of
            ([pIn], pState:pOuts) -> do
              stateInTy <- liftEither (lookupPortTy inner pIn)
              stateOutTy <- liftEither (lookupPortTy inner pState)
              if stateInTy == stateOutTy
                then pure ()
                else liftEither (Left "loop: body first output type must match input type")
              outTys <- mapM (liftEither . lookupPortTy inner) pOuts
              let (outs, diag0) = allocPorts outTys (emptyDiagram mode curIxCtx)
              diag1 <- liftEither (addEdgePayload (PFeedback inner) [] outs diag0)
              let diag2 = diag1 { dIn = [], dOut = outs }
              liftEither (validateDiagram diag2)
              pure (diag2, binderSigs')
            _ -> liftEither (Left "loop: expected exactly one input and at least one output")
        RDComp a b -> do
          (d1, binderSigs1) <- build curIxCtx binderSigs a
          (d2, binderSigs2) <- build curIxCtx binderSigs1 b
          dComp <- liftEither (compD ttDoc d2 d1)
          pure (dComp, binderSigs2)
        RDTensor a b -> do
          (d1, binderSigs1) <- build curIxCtx binderSigs a
          (d2, binderSigs2) <- build curIxCtx binderSigs1 b
          dTen <- liftEither (tensorD d1 d2)
          pure (dTen, binderSigs2)

    elaborateBinderArgs curIxCtx binderSigs binderSlots mBinderArgs =
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
                  (bsIxCtx slot)
                  tyVars
                  ixVars
                  M.empty
                  BMNoMeta
                  False
                  exprArg
              diagArg' <- liftEither (unifyBoundary ttDoc rigidTy rigidIx (bsDom slot) (bsCod slot) diagArg)
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

    elabIxArg v rawArg = liftEither (elabIxTerm doc tyVars ixVars M.empty (Just (ixvSort v)) rawArg)

    mkGenDiag curIxCtx g attrs bargs dom cod = do
      let (ins, d0) = allocPorts dom (emptyDiagram mode curIxCtx)
      let (outs, d1) = allocPorts cod d0
      d2 <- addEdgePayload (PGen g attrs bargs) ins outs d1
      let d3 = d2 { dIn = ins, dOut = outs }
      validateDiagram d3
      pure d3

    mkSpliceDiag curIxCtx meta dom cod = do
      let (ins, d0) = allocPorts dom (emptyDiagram mode curIxCtx)
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
      ixCtx' <- applySubstCtxDoc subst (bsIxCtx bs)
      dom' <- applySubstCtxDoc subst (bsDom bs)
      cod' <- applySubstCtxDoc subst (bsCod bs)
      pure bs { bsIxCtx = ixCtx', bsDom = dom', bsCod = cod' }

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

unifyBoundary :: TypeTheory -> S.Set TyVar -> S.Set IxVar -> Context -> Context -> Diagram -> Either Text Diagram
unifyBoundary tt rigidTy rigidIx dom cod diag = do
  domDiag <- diagramDom diag
  let flexTy0 = S.difference (freeTyVarsDiagram diag) rigidTy
  let flexIx0 = S.difference (freeIxVarsDiagram diag) rigidIx
  s1 <- U.unifyCtx tt (dIxCtx diag) flexTy0 flexIx0 domDiag dom
  diag1 <- applySubstDiagram tt s1 diag
  codDiag <- diagramCod diag1
  let flexTy1 = S.difference (freeTyVarsDiagram diag1) rigidTy
  let flexIx1 = S.difference (freeIxVarsDiagram diag1) rigidIx
  s2 <- U.unifyCtx tt (dIxCtx diag1) flexTy1 flexIx1 codDiag cod
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

freshIxSubst :: Int -> [IxVar] -> Fresh (M.Map IxVar IxTerm)
freshIxSubst depth vars = do
  pairs <- mapM (freshIxVar depth) vars
  pure (M.fromList pairs)

extractFreshTyVars :: [TyVar] -> M.Map TyVar TypeExpr -> Either Text [TyVar]
extractFreshTyVars vars subst =
  mapM lookupVar vars
  where
    lookupVar v =
      case M.lookup v subst of
        Just (TVar v') -> Right v'
        _ -> Left "internal error: expected fresh type variable"

extractFreshIxVars :: [IxVar] -> M.Map IxVar IxTerm -> Either Text [IxVar]
extractFreshIxVars vars subst =
  mapM lookupVar vars
  where
    lookupVar v =
      case M.lookup v subst of
        Just (IXVar v') -> Right v'
        _ -> Left "internal error: expected fresh index variable"

freshTyVar :: TyVar -> Fresh (TyVar, TypeExpr)
freshTyVar v = do
  n <- freshInt
  let name = tvName v <> T.pack ("#" <> show n)
  let fresh = TyVar { tvName = name, tvMode = tvMode v }
  pure (v, TVar fresh)

freshIxVar :: Int -> IxVar -> Fresh (IxVar, IxTerm)
freshIxVar depth v = do
  n <- freshInt
  let name = ixvName v <> T.pack ("#" <> show n)
  let fresh = IxVar { ixvName = name, ixvSort = ixvSort v, ixvScope = max (ixvScope v) depth }
  pure (v, IXVar fresh)

freshInt :: Fresh Int
freshInt = Fresh (\n -> Right (n, n + 1))

liftEither :: Either Text a -> Fresh a
liftEither (Left err) = Fresh (\_ -> Left err)
liftEither (Right a) = pure a
