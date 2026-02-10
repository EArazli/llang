{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Pushout
  ( PolyPushoutResult(..)
  , computePolyPushout
  , computePolyCoproduct
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.IntMap.Strict as IM
import Control.Monad (filterM, foldM)
import Strat.Common.Rules (RewritePolicy(..))
import Strat.Common.Rules (RuleClass(..), Orientation(..))
import Strat.Poly.Doctrine
import Strat.Poly.Morphism
import Strat.Poly.ModeTheory (ModeName(..), ModeTheory(..), ModName, ModDecl(..), ModExpr(..))
import Strat.Poly.TypeExpr
import Strat.Poly.IndexTheory (IxTheory(..), IxRule(..))
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Attr
import Strat.Poly.Diagram (Diagram(..), genD, genDWithAttrs, diagramDom, diagramCod)
import Strat.Poly.Graph (Edge(..), EdgePayload(..), BinderArg(..), renumberDiagram, diagramPortIds, diagramIsoEq)
import Strat.Poly.Cell2 (Cell2(..))


data PolyPushoutResult = PolyPushoutResult
  { poDoctrine :: Doctrine
  , poInl :: Morphism
  , poInr :: Morphism
  , poGlue :: Morphism
  } deriving (Eq, Show)

type TypeRenameMap = M.Map TypeRef TypeRef
type TypePermMap = M.Map TypeRef [Int]
type AttrSortRenameMap = M.Map AttrSort AttrSort

computePolyPushout :: Text -> Morphism -> Morphism -> Either Text PolyPushoutResult
computePolyPushout name f g = do
  ensureSameSource
  ensureIdentityModeMap f
  ensureIdentityModeMap g
  ensureSameModes (morSrc f) (morTgt f)
  ensureSameModes (morSrc g) (morTgt g)
  let mt = dModes (morSrc f)
  attrSortMapF <- requireAttrSortRenameMap f
  attrSortMapG <- requireAttrSortRenameMap g
  (typeMapF, permMapF) <- requireTypeRenameMap f
  (typeMapG, permMapG) <- requireTypeRenameMap g
  genMapF <- requireGenRenameMap f
  genMapG <- requireGenRenameMap g
  ensureInjective "attrsort" (M.elems attrSortMapF)
  ensureInjective "attrsort" (M.elems attrSortMapG)
  ensureInjective "type" (M.elems typeMapF)
  ensureInjective "type" (M.elems typeMapG)
  ensureInjective "gen" (M.elems genMapF)
  ensureInjective "gen" (M.elems genMapG)
  let renameAttrSortsB0 = M.fromList [ (img, src) | (src, img) <- M.toList attrSortMapF ]
  let renameAttrSortsC0 = M.fromList [ (img, src) | (src, img) <- M.toList attrSortMapG ]
  let renameTypesB0 = M.fromList [ (img, src) | (src, img) <- M.toList typeMapF ]
  let renameTypesC0 = M.fromList [ (img, src) | (src, img) <- M.toList typeMapG ]
  let permTypesB0 = permMapF
  let permTypesC0 = permMapG
  let renameGensB0 = M.fromList [ ((m, img), src) | ((m, src), img) <- M.toList genMapF ]
  let renameGensC0 = M.fromList [ ((m, img), src) | ((m, src), img) <- M.toList genMapG ]
  let prefixB = sanitizePrefix (dName (morTgt f)) <> "_inl"
  let prefixC = sanitizePrefix (dName (morTgt g)) <> "_inr"
  let renameAttrSortsB = M.union renameAttrSortsB0 (disjointAttrSortRenames prefixB (morSrc f) renameAttrSortsB0 (morTgt f))
  let renameAttrSortsC = M.union renameAttrSortsC0 (disjointAttrSortRenames prefixC (morSrc f) renameAttrSortsC0 (morTgt g))
  let renameTypesB = M.union renameTypesB0 (disjointTypeRenames prefixB (morSrc f) renameTypesB0 (morTgt f))
  let renameTypesC = M.union renameTypesC0 (disjointTypeRenames prefixC (morSrc f) renameTypesC0 (morTgt g))
  let renameGensB = M.union renameGensB0 (disjointGenRenames prefixB (morSrc f) renameGensB0 (morTgt f))
  let renameGensC = M.union renameGensC0 (disjointGenRenames prefixC (morSrc f) renameGensC0 (morTgt g))
  let renameCellsB = disjointCellRenames prefixB (morSrc f) (morTgt f)
  let renameCellsC = disjointCellRenames prefixC (morSrc f) (morTgt g)
  b' <- renameDoctrine renameAttrSortsB renameTypesB permTypesB0 renameGensB renameCellsB (morTgt f)
  c' <- renameDoctrine renameAttrSortsC renameTypesC permTypesC0 renameGensC renameCellsC (morTgt g)
  merged <- mergeDoctrineList mt [morSrc f, b', c']
  let pres = merged { dName = name }
  glue <- buildGlue name (morSrc f) pres
  inl <- buildInj (name <> ".inl") (morTgt f) pres renameAttrSortsB renameTypesB permTypesB0 renameGensB
  inr <- buildInj (name <> ".inr") (morTgt g) pres renameAttrSortsC renameTypesC permTypesC0 renameGensC
  checkGenerated "glue" glue
  checkGenerated "inl" inl
  checkGenerated "inr" inr
  pure PolyPushoutResult { poDoctrine = pres, poInl = inl, poInr = inr, poGlue = glue }
  where
    ensureSameSource =
      if morSrc f == morSrc g
        then Right ()
        else Left "poly pushout requires morphisms with the same source"
    ensureIdentityModeMap mor =
      let modes = M.keys (mtModes (dModes (morSrc mor)))
          mods = M.toList (mtDecls (dModes (morSrc mor)))
          okModes = all (\m -> M.lookup m (morModeMap mor) == Just m) modes
          okMods =
            all
              (\(name, decl) ->
                M.lookup name (morModMap mor)
                  == Just (ModExpr { meSrc = mdSrc decl, meTgt = mdTgt decl, mePath = [name] }))
              mods
      in if okModes && okMods
        then Right ()
        else Left "pushout requires mode-preserving morphisms"

computePolyCoproduct :: Text -> Doctrine -> Doctrine -> Either Text PolyPushoutResult
computePolyCoproduct name a b = do
  ensureSameModes a b
  let empty = Doctrine
        { dName = "Empty"
        , dModes = dModes a
        , dIndexModes = S.empty
        , dIxTheory = M.empty
        , dAttrSorts = M.empty
        , dTypes = M.empty
        , dGens = M.empty
        , dCells2 = []
        }
  let modeMap = identityModeMap empty
  let morA = Morphism
        { morName = "coproduct.inl0"
        , morSrc = empty
        , morTgt = a
        , morIsCoercion = True
        , morModeMap = modeMap
        , morModMap = identityModMap empty
        , morAttrSortMap = M.empty
        , morTypeMap = M.empty
        , morGenMap = M.empty
        , morIxFunMap = M.empty
        , morPolicy = UseAllOriented
        , morFuel = 50
        }
  let morB = Morphism
        { morName = "coproduct.inr0"
        , morSrc = empty
        , morTgt = b
        , morIsCoercion = True
        , morModeMap = modeMap
        , morModMap = identityModMap empty
        , morAttrSortMap = M.empty
        , morTypeMap = M.empty
        , morGenMap = M.empty
        , morIxFunMap = M.empty
        , morPolicy = UseAllOriented
        , morFuel = 50
        }
  computePolyPushout name morA morB

ensureSameModes :: Doctrine -> Doctrine -> Either Text ()
ensureSameModes a b =
  if dModes a == dModes b
    then Right ()
    else Left "poly pushout requires identical mode theories"

identityModeMap :: Doctrine -> M.Map ModeName ModeName
identityModeMap doc =
  M.fromList [ (m, m) | m <- M.keys (mtModes (dModes doc)) ]

identityModMap :: Doctrine -> M.Map ModName ModExpr
identityModMap doc =
  M.fromList
    [ (name, ModExpr { meSrc = mdSrc decl, meTgt = mdTgt decl, mePath = [name] })
    | (name, decl) <- M.toList (mtDecls (dModes doc))
    ]

identityAttrSortMap :: Doctrine -> M.Map AttrSort AttrSort
identityAttrSortMap doc =
  M.fromList [ (s, s) | s <- M.keys (dAttrSorts doc) ]

requireTypeRenameMap :: Morphism -> Either Text (TypeRenameMap, TypePermMap)
requireTypeRenameMap mor = do
  let src = morSrc mor
  let types = allTypes src
  entries <- mapM (typeImage mor) types
  let typeMap = M.fromList [ (srcRef, tgtRef) | (srcRef, tgtRef, _) <- entries ]
  permMap <- foldM insertPerm M.empty entries
  pure (typeMap, permMap)
  where
    typeImage m (srcRef, sig) = do
      (tgtRef, mPerm) <- case M.lookup srcRef (morTypeMap m) of
        Nothing -> Right (srcRef, Nothing)
        Just tmpl -> templateTarget tmpl (tsParams sig)
      ensureTypeExists (morTgt m) tgtRef (length (tsParams sig))
      pure (srcRef, tgtRef, mPerm)
    insertPerm mp (_srcRef, tgtRef, mPerm) =
      case mPerm of
        Nothing -> Right mp
        Just perm ->
          case M.lookup tgtRef mp of
            Nothing -> Right (M.insert tgtRef perm mp)
            Just existing
              | existing == perm -> Right mp
              | otherwise -> Left "poly pushout: inconsistent type permutation"
    templateTarget tmpl srcParams =
      case ttBody tmpl of
        TCon tgtRef args
          | length (ttParams tmpl) == arity
          , length args == arity
          , positionalKindMatch (zip srcParams (ttParams tmpl))
          , let positions = map (argParamIndex (ttParams tmpl)) args
          , all isJust positions
          , let perm = [ i | Just i <- positions ]
          , length perm == S.size (S.fromList perm)
          -> do
            inv <- invertPermutation arity perm
            let ident = [0 .. arity - 1]
            let inv' = if perm == ident then Nothing else Just inv
            pure (tgtRef, inv')
        _ -> Left "poly pushout requires renaming type maps"
      where
        arity = length srcParams

    positionalKindMatch [] = True
    positionalKindMatch ((srcParam, tmplParam):rest) =
      kindMatch srcParam tmplParam && positionalKindMatch rest

    kindMatch srcParam tmplParam =
      case (srcParam, tmplParam) of
        (PS_Ty _, TPType _) -> True
        (PS_Ix _, TPIx _) -> True
        _ -> False

    argParamIndex params arg =
      case arg of
        TAType (TVar v) ->
          findParamIndex params (\p -> case p of TPType v' -> v' == v; _ -> False)
        TAIndex (IXVar v) ->
          findParamIndex params (\p -> case p of TPIx v' -> v' == v; _ -> False)
        _ -> Nothing

    findParamIndex params p =
      case [ i | (i, param) <- zip [0 :: Int ..] params, p param ] of
        [i] -> Just i
        _ -> Nothing

    isJust mv =
      case mv of
        Just _ -> True
        Nothing -> False

requireAttrSortRenameMap :: Morphism -> Either Text AttrSortRenameMap
requireAttrSortRenameMap mor = do
  let srcSorts = M.keys (dAttrSorts (morSrc mor))
  let tgtSorts = dAttrSorts (morTgt mor)
  let mapOne srcSort =
        case M.lookup srcSort (morAttrSortMap mor) of
          Nothing -> Left "poly pushout requires explicit attrsort mappings"
          Just tgtSort ->
            if M.member tgtSort tgtSorts
              then Right (srcSort, tgtSort)
              else Left "poly pushout: target attrsort missing"
  pairs <- mapM mapOne srcSorts
  pure (M.fromList pairs)

invertPermutation :: Int -> [Int] -> Either Text [Int]
invertPermutation n perm
  | length perm /= n = Left "poly pushout: type permutation arity mismatch"
  | any outOfRange perm = Left "poly pushout: type permutation index out of range"
  | length (S.fromList perm) /= n = Left "poly pushout: type permutation is not a bijection"
  | otherwise =
      let mp = IM.fromList (zip perm [0..])
      in Right [ mp IM.! i | i <- [0..n-1] ]
  where
    outOfRange i = i < 0 || i >= n

requireGenRenameMap :: Morphism -> Either Text (M.Map (ModeName, GenName) GenName)
requireGenRenameMap mor = do
  let src = morSrc mor
  let gens = allGens src
  fmap M.fromList (mapM (genImage mor) gens)
  where
    genImage m (mode, gen) = do
      img <- case M.lookup (mode, gdName gen) (morGenMap m) of
        Nothing -> Left "poly pushout requires explicit generator mappings"
        Just d -> do
          imgName <- singleGenName m gen d
          ensureGenExists (morTgt m) mode imgName
          Right imgName
      pure ((mode, gdName gen), img)

singleGenName :: Morphism -> GenDecl -> Diagram -> Either Text GenName
singleGenName mor srcGen diag = do
  canon <- renumberDiagram diag
  case IM.elems (dEdges canon) of
    [edge] -> do
      let boundary = dIn canon <> dOut canon
      let edgePorts = eIns edge <> eOuts edge
      let allPorts = diagramPortIds canon
      expectedAttrs <- expectedAttrMap mor srcGen
      case ePayload edge of
        PGen g attrs bargs ->
          if boundary == edgePorts && length allPorts == length boundary && null bargs && attrs == expectedAttrs
            then Right g
            else Left "poly pushout requires generator mappings to be a single generator"
        _ -> Left "poly pushout requires generator mappings to be a single generator"
    _ -> Left "poly pushout requires generator mappings to be a single generator"
  where
    expectedAttrMap m gen = fmap M.fromList (mapM toField (gdAttrs gen))
      where
        toField (fieldName, srcSort) = do
          tgtSort <-
            case M.lookup srcSort (morAttrSortMap m) of
              Nothing -> Left "poly pushout: missing attrsort mapping in generator image"
              Just s -> Right s
          Right (fieldName, ATVar (AttrVar fieldName tgtSort))

ensureTypeExists :: Doctrine -> TypeRef -> Int -> Either Text ()
ensureTypeExists doc ref arity =
  case lookupTypeSig doc ref of
    Left _ -> Left "poly pushout: target type missing"
    Right sig
      | length (tsParams sig) == arity -> Right ()
      | otherwise -> Left "poly pushout: target type arity mismatch"

ensureGenExists :: Doctrine -> ModeName -> GenName -> Either Text ()
ensureGenExists doc mode name =
  case M.lookup mode (dGens doc) >>= M.lookup name of
    Nothing -> Left "poly pushout: target generator missing"
    Just _ -> Right ()

ensureInjective :: Ord a => Text -> [a] -> Either Text ()
ensureInjective label images =
  case firstDup images of
    Nothing -> Right ()
    Just _ -> Left ("poly pushout requires injective " <> label <> " mapping")
  where
    firstDup xs = go S.empty xs
    go _ [] = Nothing
    go seen (x:rest)
      | x `S.member` seen = Just x
      | otherwise = go (S.insert x seen) rest

disjointTypeRenames :: Text -> Doctrine -> TypeRenameMap -> Doctrine -> TypeRenameMap
disjointTypeRenames prefix src interfaceRen tgt =
  foldl add M.empty (M.toList (dTypes tgt))
  where
    srcNames = namesByMode [ (trMode ref, trName ref) | (ref, _) <- allTypes src ]
    add acc (mode, table) =
      let reserved = M.findWithDefault S.empty mode srcNames
          names = M.keys table
          (_, mp) = foldl (step mode) (reserved, M.empty) names
      in M.union acc mp
    step mode (used, mp) name =
      let key = TypeRef mode name
      in if M.member key interfaceRen
        then (used, mp)
        else
          let (name', used') = freshTypeName prefix name used
              key' = TypeRef mode name'
          in (used', M.insert key key' mp)

disjointAttrSortRenames :: Text -> Doctrine -> AttrSortRenameMap -> Doctrine -> AttrSortRenameMap
disjointAttrSortRenames prefix src interfaceRen tgt =
  let reserved = S.fromList (M.keys (dAttrSorts src))
      names = M.keys (dAttrSorts tgt)
      (_, mp) = foldl step (reserved, M.empty) names
  in mp
  where
    step (used, mp) name =
      if M.member name interfaceRen
        then (used, mp)
        else
          let (name', used') = freshAttrSortName prefix name used
          in (used', M.insert name name' mp)

disjointGenRenames :: Text -> Doctrine -> M.Map (ModeName, GenName) GenName -> Doctrine -> M.Map (ModeName, GenName) GenName
disjointGenRenames prefix src interfaceRen tgt =
  foldl add M.empty (M.toList (dGens tgt))
  where
    srcNames = namesByMode [ (mode, gdName gen) | (mode, gen) <- allGens src ]
    add acc (mode, table) =
      let reserved = M.findWithDefault S.empty mode srcNames
          names = map gdName (M.elems table)
          (_, mp) = foldl (step mode) (reserved, M.empty) names
      in M.union acc mp
    step mode (used, mp) name =
      let key = (mode, name)
      in if M.member key interfaceRen
        then (used, mp)
        else
          let (name', used') = freshGenName prefix name used
          in (used', M.insert key name' mp)

disjointCellRenames :: Text -> Doctrine -> Doctrine -> M.Map (ModeName, Text) Text
disjointCellRenames prefix src tgt =
  snd (foldl step (srcNames, M.empty) (dCells2 tgt))
  where
    srcNames = namesByMode [ (dMode (c2LHS cell), c2Name cell) | cell <- dCells2 src ]
    step (usedByMode, mp) cell =
      let mode = dMode (c2LHS cell)
          name = c2Name cell
          used = M.findWithDefault S.empty mode usedByMode
      in if name `S.member` used
        then (usedByMode, mp)
        else
          let (name', used') = freshCellName prefix name used
              usedByMode' = M.insert mode used' usedByMode
          in (usedByMode', M.insert (mode, name) name' mp)

namesByMode :: (Ord a) => [(ModeName, a)] -> M.Map ModeName (S.Set a)
namesByMode pairs =
  foldl add M.empty pairs
  where
    add mp (mode, name) =
      let set = M.findWithDefault S.empty mode mp
      in M.insert mode (S.insert name set) mp

sanitizePrefix :: Text -> Text
sanitizePrefix = T.map (\c -> if c == '.' then '_' else c)

freshTypeName :: Text -> TypeName -> S.Set TypeName -> (TypeName, S.Set TypeName)
freshTypeName prefix (TypeName base) used =
  let baseName = prefix <> "_" <> base
      candidate = TypeName baseName
  in freshen candidate (\n -> TypeName (baseName <> "_" <> T.pack (show n))) used

freshAttrSortName :: Text -> AttrSort -> S.Set AttrSort -> (AttrSort, S.Set AttrSort)
freshAttrSortName prefix (AttrSort base) used =
  let baseName = prefix <> "_" <> base
      candidate = AttrSort baseName
  in freshen candidate (\n -> AttrSort (baseName <> "_" <> T.pack (show n))) used

freshGenName :: Text -> GenName -> S.Set GenName -> (GenName, S.Set GenName)
freshGenName prefix (GenName base) used =
  let baseName = prefix <> "_" <> base
      candidate = GenName baseName
  in freshen candidate (\n -> GenName (baseName <> "_" <> T.pack (show n))) used

freshCellName :: Text -> Text -> S.Set Text -> (Text, S.Set Text)
freshCellName prefix base used =
  let baseName = prefix <> "_" <> base
      candidate = baseName
  in freshen candidate (\n -> baseName <> "_" <> T.pack (show n)) used

freshen :: (Ord a) => a -> (Int -> a) -> S.Set a -> (a, S.Set a)
freshen candidate mk used =
  if candidate `S.member` used
    then go 1
    else (candidate, S.insert candidate used)
  where
    go n =
      let cand = mk n
      in if cand `S.member` used
        then go (n + 1)
        else (cand, S.insert cand used)

renameDoctrine
  :: AttrSortRenameMap
  -> TypeRenameMap
  -> TypePermMap
  -> M.Map (ModeName, GenName) GenName
  -> M.Map (ModeName, Text) Text
  -> Doctrine
  -> Either Text Doctrine
renameDoctrine attrRen tyRen permRen genRen cellRen doc = do
  attrSorts' <- renameAttrSorts attrRen (dAttrSorts doc)
  types' <- M.traverseWithKey renameTypeTable (dTypes doc)
  gens' <- M.traverseWithKey renameGenTable (dGens doc)
  cells' <- mapM (renameCell attrRen tyRen permRen genRen cellRen) (dCells2 doc)
  pure doc { dAttrSorts = attrSorts', dTypes = types', dGens = gens', dCells2 = cells' }
  where
    renameAttrSorts ren table =
      foldl add (Right M.empty) (M.elems table)
      where
        add acc decl = do
          mp <- acc
          let name' = M.findWithDefault (asName decl) (asName decl) ren
          let decl' = decl { asName = name' }
          case M.lookup name' mp of
            Nothing -> Right (M.insert name' decl' mp)
            Just existing | existing == decl' -> Right mp
            _ -> Left "poly pushout: attribute sort collision"
    renameTypeTable mode table =
      foldl add (Right M.empty) (M.toList table)
      where
        add acc (name, sig) = do
          mp <- acc
          let ref = TypeRef mode name
          let ref' = M.findWithDefault ref ref tyRen
          if trMode ref' /= mode
            then Left "poly pushout: type rename mode mismatch"
            else case M.lookup (trName ref') mp of
              Nothing -> Right (M.insert (trName ref') sig mp)
              Just existing | existing == sig -> Right mp
              _ -> Left "poly pushout: type name collision"
    renameGenTable mode table =
      foldl add (Right M.empty) (M.elems table)
      where
        add acc gen = do
          mp <- acc
          let name' = M.findWithDefault (gdName gen) (mode, gdName gen) genRen
          dom' <- mapM (renameInputShape tyRen permRen) (gdDom gen)
          cod' <- mapM (renameTypeExpr tyRen permRen) (gdCod gen)
          let attrs' = [ (fieldName, M.findWithDefault sortName sortName attrRen) | (fieldName, sortName) <- gdAttrs gen ]
          let gen' = gen { gdName = name', gdDom = dom', gdCod = cod', gdAttrs = attrs' }
          case M.lookup name' mp of
            Nothing -> Right (M.insert name' gen' mp)
            Just existing | existing == gen' -> Right mp
            _ -> Left "poly pushout: generator name collision"

renameCell
  :: AttrSortRenameMap
  -> TypeRenameMap
  -> TypePermMap
  -> M.Map (ModeName, GenName) GenName
  -> M.Map (ModeName, Text) Text
  -> Cell2
  -> Either Text Cell2
renameCell attrRen tyRen permRen genRen cellRen cell = do
  let mode = dMode (c2LHS cell)
  let name' = M.findWithDefault (c2Name cell) (mode, c2Name cell) cellRen
  lhs' <- renameDiagram attrRen tyRen permRen genRen (c2LHS cell)
  rhs' <- renameDiagram attrRen tyRen permRen genRen (c2RHS cell)
  pure cell
    { c2Name = name'
    , c2LHS = lhs'
    , c2RHS = rhs'
    }

renameDiagram :: AttrSortRenameMap -> TypeRenameMap -> TypePermMap -> M.Map (ModeName, GenName) GenName -> Diagram -> Either Text Diagram
renameDiagram attrRen tyRen permRen genRen diag = do
  let mode = dMode diag
  dIxCtx' <- mapM (renameTypeExpr tyRen permRen) (dIxCtx diag)
  dPortTy' <- traverse (renameTypeExpr tyRen permRen) (dPortTy diag)
  dEdges' <- traverse (renameEdge mode) (dEdges diag)
  pure diag { dIxCtx = dIxCtx', dPortTy = dPortTy', dEdges = dEdges' }
  where
    renameEdge mode edge =
      case ePayload edge of
        PGen gen attrs bargs -> do
          let gen' = M.findWithDefault gen (mode, gen) genRen
              attrs' = M.map (renameAttrSortTerm attrRen) attrs
          bargs' <- mapM renameBinderArg bargs
          pure edge { ePayload = PGen gen' attrs' bargs' }
        PBox name inner -> do
          inner' <- renameDiagram attrRen tyRen permRen genRen inner
          pure edge { ePayload = PBox name inner' }
        PSplice x ->
          pure edge { ePayload = PSplice x }

    renameBinderArg barg =
      case barg of
        BAConcrete inner -> BAConcrete <$> renameDiagram attrRen tyRen permRen genRen inner
        BAMeta x -> Right (BAMeta x)

renameAttrSortTerm :: AttrSortRenameMap -> AttrTerm -> AttrTerm
renameAttrSortTerm ren term =
  case term of
    ATLit lit -> ATLit lit
    ATVar v ->
      let sortName' = M.findWithDefault (avSort v) (avSort v) ren
      in ATVar v { avSort = sortName' }

renameInputShape :: TypeRenameMap -> TypePermMap -> InputShape -> Either Text InputShape
renameInputShape ren permRen shape =
  case shape of
    InPort ty -> InPort <$> renameTypeExpr ren permRen ty
    InBinder bs -> do
      ix' <- mapM (renameTypeExpr ren permRen) (bsIxCtx bs)
      dom' <- mapM (renameTypeExpr ren permRen) (bsDom bs)
      cod' <- mapM (renameTypeExpr ren permRen) (bsCod bs)
      Right (InBinder bs { bsIxCtx = ix', bsDom = dom', bsCod = cod' })

renameTypeExpr :: TypeRenameMap -> TypePermMap -> TypeExpr -> Either Text TypeExpr
renameTypeExpr ren permRen ty =
  case ty of
    TVar v -> Right (TVar v)
    TMod me inner -> do
      inner' <- renameTypeExpr ren permRen inner
      Right (TMod me inner')
    TCon ref args -> do
      args' <- mapM renameArg args
      let ref' = M.findWithDefault ref ref ren
      case M.lookup ref permRen of
        Nothing -> Right (TCon ref' args')
        Just perm -> do
          args'' <- applyPerm perm args'
          Right (TCon ref' args'')
  where
    renameArg arg =
      case arg of
        TAType t -> TAType <$> renameTypeExpr ren permRen t
        TAIndex ix -> TAIndex <$> renameIx ix

    renameIx ix =
      case ix of
        IXVar v -> do
          sort' <- renameTypeExpr ren permRen (ixvSort v)
          Right (IXVar v { ixvSort = sort' })
        IXBound i -> Right (IXBound i)
        IXFun f args -> IXFun f <$> mapM renameIx args

applyPerm :: [Int] -> [a] -> Either Text [a]
applyPerm perm args
  | length perm /= n = Left "poly pushout: type permutation arity mismatch"
  | any outOfRange perm = Left "poly pushout: type permutation index out of range"
  | length (S.fromList perm) /= n = Left "poly pushout: type permutation is not a bijection"
  | otherwise = Right [ args !! i | i <- perm ]
  where
    n = length args
    outOfRange i = i < 0 || i >= n

mergeDoctrineList :: ModeTheory -> [Doctrine] -> Either Text Doctrine
mergeDoctrineList _ [] = Left "poly pushout: no doctrines to merge"
mergeDoctrineList mt (d:ds) = foldl merge (Right d) ds
  where
    merge acc next = do
      base <- acc
      mergeDoctrine mt base next

mergeDoctrine :: ModeTheory -> Doctrine -> Doctrine -> Either Text Doctrine
mergeDoctrine mt a b = do
  if dModes a /= dModes b
    then Left "poly pushout: mode mismatch"
    else do
      attrSorts <- mergeAttrSorts (dAttrSorts a) (dAttrSorts b)
      indexModes <- pure (S.union (dIndexModes a) (dIndexModes b))
      ixTheory <- mergeIxTheoryTables (dIxTheory a) (dIxTheory b)
      types <- mergeTypeTables (dTypes a) (dTypes b)
      gens <- mergeGenTables (dGens a) (dGens b)
      cells <- mergeCells mt (dCells2 a) (dCells2 b)
      let merged =
            a
              { dIndexModes = indexModes
              , dIxTheory = ixTheory
              , dAttrSorts = attrSorts
              , dTypes = types
              , dGens = gens
              , dCells2 = cells
              }
      validateDoctrine merged
      pure merged
  where
    mergeAttrSorts left right =
      foldl add (Right left) (M.toList right)
      where
        add acc (name, decl) = do
          mp <- acc
          case M.lookup name mp of
            Nothing -> Right (M.insert name decl mp)
            Just existing | existing == decl -> Right mp
            _ -> Left "poly pushout: attribute sort conflict"
    mergeTypeTables left right =
      foldl mergeTypeMode (Right left) (M.toList right)
    mergeTypeMode acc (mode, table) = do
      mp <- acc
      let base = M.findWithDefault M.empty mode mp
      merged <- mergeTypeTable base table
      pure (M.insert mode merged mp)
    mergeTypeTable left right =
      foldl add (Right left) (M.toList right)
      where
        add acc (name, sig) = do
          mp <- acc
          case M.lookup name mp of
            Nothing -> Right (M.insert name sig mp)
            Just a | a == sig -> Right mp
            _ -> Left "poly pushout: type signature conflict"
    mergeGenTables left right =
      foldl mergeGenMode (Right left) (M.toList right)
    mergeGenMode acc (mode, table) = do
      mp <- acc
      let base = M.findWithDefault M.empty mode mp
      merged <- mergeGenTable base table
      pure (M.insert mode merged mp)
    mergeGenTable left right =
      foldl add (Right left) (M.elems right)
      where
        add acc gen = do
          mp <- acc
          case M.lookup (gdName gen) mp of
            Nothing -> Right (M.insert (gdName gen) gen mp)
            Just g | genDeclAlphaEq g gen -> Right mp
            _ -> Left "poly pushout: generator conflict"

    mergeIxTheoryTables left right =
      foldl mergeMode (Right left) (M.toList right)
      where
        mergeMode acc (mode, theory) = do
          mp <- acc
          let base = M.findWithDefault (IxTheory M.empty []) mode mp
          merged <- mergeIxTheory mode base theory
          pure (M.insert mode merged mp)

    mergeIxTheory mode left right = do
      funs <- mergeIxFuns (itFuns left) (itFuns right)
      rules <- mergeIxRules (itRules left) (itRules right)
      pure IxTheory { itFuns = funs, itRules = rules }
      where
        mergeIxFuns leftF rightF =
          foldl addFun (Right leftF) (M.toList rightF)
          where
            addFun acc (fname, sig) = do
              mp <- acc
              case M.lookup fname mp of
                Nothing -> Right (M.insert fname sig mp)
                Just sig0 | sig0 == sig -> Right mp
                _ -> Left ("poly pushout: index_fun signature conflict in mode " <> renderMode mode)

        mergeIxRules leftR rightR = do
          let combined = dedupeRules (leftR <> rightR)
          if hasRuleConflict combined
            then Left ("poly pushout: index_rule conflict in mode " <> renderMode mode)
            else Right combined

        dedupeRules = foldl add []
          where
            add acc r =
              if any (== r) acc then acc else acc <> [r]

        hasRuleConflict rules =
          let lhsMap = M.fromListWith S.union [ (irLHS rule, S.singleton (irRHS rule)) | rule <- rules ]
           in any (\rhsSet -> S.size rhsSet > 1) (M.elems lhsMap)

        renderMode (ModeName name) = name

mergeCells :: ModeTheory -> [Cell2] -> [Cell2] -> Either Text [Cell2]
mergeCells mt left right =
  foldl insertCell (Right []) (left <> right)
  where
    insertCell acc cell = do
      cells <- acc
      case findNameCollision cell cells of
        Just existing ->
          if bodiesIso cell existing
            then Right (replaceCell existing (mergeCell existing cell) cells)
            else Left ("poly pushout: cell name conflict (" <> c2Name existing <> ", " <> c2Name cell <> ") " <> renderCellDiff existing cell)
        Nothing -> do
          match <- findMatch cell cells
          case match of
            Nothing -> Right (cells <> [cell])
            Just existing ->
              Right (replaceCell existing (mergeCell existing cell) cells)

    findMatch cell cells = do
      matches <- filterM (cellBodyEq cell) cells
      case matches of
        [] -> Right Nothing
        (c:_) -> Right (Just c)

    findNameCollision cell cells =
      case filter (\c -> c2Name c == c2Name cell) cells of
        (c:_) -> Just c
        [] -> Nothing

    bodiesIso a b =
      case cellBodyEq a b of
        Left _ -> False
        Right ok -> ok

    replaceCell target newCell cells =
      let (before, after) = break (\c -> c2Name c == c2Name target) cells
      in case after of
          [] -> cells
          (_:rest) -> before <> [newCell] <> rest

    mergeCell existing incoming =
      let mergedClass =
            if c2Class existing == Structural || c2Class incoming == Structural
              then Structural
              else Computational
          mergedOrient = orientJoin (c2Orient existing) (c2Orient incoming)
      in existing { c2Class = mergedClass, c2Orient = mergedOrient }

    orientJoin a b =
      case (a, b) of
        (Bidirectional, _) -> Bidirectional
        (_, Bidirectional) -> Bidirectional
        (LR, RL) -> Bidirectional
        (RL, LR) -> Bidirectional
        (LR, LR) -> LR
        (RL, RL) -> RL
        (Unoriented, x) -> x
        (x, Unoriented) -> x

    renderCellDiff a b =
      "(" <> renderCellHeader a <> " vs " <> renderCellHeader b <> ")"

    renderCellHeader cell =
      let modeTxt = renderMode (dMode (c2LHS cell))
          domTxt = renderCtx (diagramDom (c2LHS cell))
          codTxt = renderCtx (diagramCod (c2LHS cell))
      in "mode=" <> modeTxt <> ", dom=" <> domTxt <> ", cod=" <> codTxt

    renderCtx res =
      case res of
        Left _ -> "<error>"
        Right ctx -> T.pack (show ctx)

    renderMode (ModeName t) = t

    cellBodyEq a b = do
      if dMode (c2LHS a) /= dMode (c2LHS b)
        then Right False
      else if length (c2TyVars a) /= length (c2TyVars b)
        then Right False
      else if length (c2IxVars a) /= length (c2IxVars b)
        then Right False
        else do
          b' <- alphaRenameCellTo (c2TyVars b) (c2TyVars a) (c2IxVars b) (c2IxVars a) b
          lhsA <- normalizeDiagramModes mt (c2LHS a)
          lhsB <- normalizeDiagramModes mt (c2LHS b')
          rhsA <- normalizeDiagramModes mt (c2RHS a)
          rhsB <- normalizeDiagramModes mt (c2RHS b')
          okL <- isoOrFalse lhsA lhsB
          okR <- isoOrFalse rhsA rhsB
          pure (okL && okR)

    isoOrFalse d1 d2 =
      case diagramIsoEq d1 d2 of
        Left _ -> Right False
        Right ok -> Right ok

genDeclAlphaEq :: GenDecl -> GenDecl -> Bool
genDeclAlphaEq g1 g2 =
  gdMode g1 == gdMode g2
    && gdName g1 == gdName g2
    && gdAttrs g1 == gdAttrs g2
    && length (gdTyVars g1) == length (gdTyVars g2)
    && length (gdIxVars g1) == length (gdIxVars g2)
    && let tyMap = M.fromList (zip (gdTyVars g2) (gdTyVars g1))
           ixMap = M.fromList (zip (gdIxVars g2) (gdIxVars g1))
           tyVars2 = map (renameTyVarAlpha tyMap) (gdTyVars g2)
           ixVars2 = map (renameIxVarAlpha tyMap ixMap) (gdIxVars g2)
           dom2 = map (renameInputShapeAlpha tyMap ixMap) (gdDom g2)
           cod2 = map (renameTypeAlpha tyMap ixMap) (gdCod g2)
       in tyVars2 == gdTyVars g1
            && ixVars2 == gdIxVars g1
            && dom2 == gdDom g1
            && cod2 == gdCod g1

alphaRenameCellTo :: [TyVar] -> [TyVar] -> [IxVar] -> [IxVar] -> Cell2 -> Either Text Cell2
alphaRenameCellTo fromTy toTy fromIx toIx cell
  | length fromTy /= length toTy = Left "poly pushout: alpha rename type arity mismatch"
  | length fromIx /= length toIx = Left "poly pushout: alpha rename index arity mismatch"
  | otherwise =
      let tyMap = M.fromList (zip fromTy toTy)
          ixMap = M.fromList (zip fromIx toIx)
          lhs' = renameDiagramAlpha tyMap ixMap (c2LHS cell)
          rhs' = renameDiagramAlpha tyMap ixMap (c2RHS cell)
      in Right cell { c2TyVars = toTy, c2IxVars = toIx, c2LHS = lhs', c2RHS = rhs' }

renameTyVarAlpha :: M.Map TyVar TyVar -> TyVar -> TyVar
renameTyVarAlpha tyMap v =
  M.findWithDefault v v tyMap

renameIxVarAlpha :: M.Map TyVar TyVar -> M.Map IxVar IxVar -> IxVar -> IxVar
renameIxVarAlpha tyMap ixMap v =
  case M.lookup v ixMap of
    Just v' -> v'
    Nothing -> v { ixvSort = renameTypeAlpha tyMap ixMap (ixvSort v) }

renameTypeAlpha :: M.Map TyVar TyVar -> M.Map IxVar IxVar -> TypeExpr -> TypeExpr
renameTypeAlpha tyMap ixMap = mapTypeExpr renameTy renameIx
  where
    renameTy ty =
      case ty of
        TVar v -> TVar (renameTyVarAlpha tyMap v)
        _ -> ty
    renameIx tm =
      case tm of
        IXVar v -> IXVar (renameIxVarAlpha tyMap ixMap v)
        _ -> tm

renameInputShapeAlpha :: M.Map TyVar TyVar -> M.Map IxVar IxVar -> InputShape -> InputShape
renameInputShapeAlpha tyMap ixMap shape =
  case shape of
    InPort ty -> InPort (renameTypeAlpha tyMap ixMap ty)
    InBinder bs ->
      let ixCtx' = map (renameTypeAlpha tyMap ixMap) (bsIxCtx bs)
          dom' = map (renameTypeAlpha tyMap ixMap) (bsDom bs)
          cod' = map (renameTypeAlpha tyMap ixMap) (bsCod bs)
      in InBinder bs { bsIxCtx = ixCtx', bsDom = dom', bsCod = cod' }

renameDiagramAlpha :: M.Map TyVar TyVar -> M.Map IxVar IxVar -> Diagram -> Diagram
renameDiagramAlpha tyMap ixMap diag =
  diag
    { dIxCtx = map (renameTypeAlpha tyMap ixMap) (dIxCtx diag)
    , dPortTy = IM.map (renameTypeAlpha tyMap ixMap) (dPortTy diag)
    , dEdges = IM.map renameEdge (dEdges diag)
    }
  where
    renameEdge edge =
      case ePayload edge of
        PGen g attrs bargs ->
          edge { ePayload = PGen g attrs (map renameBinderArg bargs) }
        PBox name inner ->
          edge { ePayload = PBox name (renameDiagramAlpha tyMap ixMap inner) }
        PSplice x ->
          edge { ePayload = PSplice x }

    renameBinderArg barg =
      case barg of
        BAConcrete inner -> BAConcrete (renameDiagramAlpha tyMap ixMap inner)
        BAMeta x -> BAMeta x

normalizeDiagramModes :: ModeTheory -> Diagram -> Either Text Diagram
normalizeDiagramModes mt diag = do
  ixCtx' <- mapM normalizeTypeModes (dIxCtx diag)
  portTy' <- traverse normalizeTypeModes (dPortTy diag)
  edges' <- traverse normalizeEdgeModes (dEdges diag)
  pure diag { dIxCtx = ixCtx', dPortTy = portTy', dEdges = edges' }
  where
    normalizeEdgeModes edge =
      case ePayload edge of
        PGen g attrs bargs -> do
          bargs' <- mapM normalizeBinderArg bargs
          pure edge { ePayload = PGen g attrs bargs' }
        PBox name inner -> do
          inner' <- normalizeDiagramModes mt inner
          pure edge { ePayload = PBox name inner' }
        PSplice x ->
          pure edge { ePayload = PSplice x }

    normalizeBinderArg barg =
      case barg of
        BAConcrete inner -> BAConcrete <$> normalizeDiagramModes mt inner
        BAMeta x -> Right (BAMeta x)

    normalizeTypeModes ty = do
      ty' <- goType ty
      normalizeTypeExpr mt ty'

    goType ty =
      case ty of
        TVar _ -> Right ty
        TCon ref args -> do
          args' <- mapM goArg args
          Right (TCon ref args')
        TMod me inner -> do
          inner' <- goType inner
          Right (TMod me inner')

    goArg arg =
      case arg of
        TAType ty -> TAType <$> goType ty
        TAIndex ix -> TAIndex <$> goIx ix

    goIx ix =
      case ix of
        IXVar v -> do
          sort' <- goType (ixvSort v)
          Right (IXVar v { ixvSort = sort' })
        IXBound i -> Right (IXBound i)
        IXFun f args -> IXFun f <$> mapM goIx args

buildGlue :: Text -> Doctrine -> Doctrine -> Either Text Morphism
buildGlue name src tgt = do
  genMap <- buildGenMap src tgt M.empty M.empty M.empty M.empty
  pure Morphism
    { morName = name <> ".glue"
    , morSrc = src
    , morTgt = tgt
    , morIsCoercion = True
    , morModeMap = identityModeMap src
    , morModMap = identityModMap src
    , morAttrSortMap = identityAttrSortMap src
    , morTypeMap = M.empty
    , morGenMap = genMap
    , morIxFunMap = M.empty
    , morPolicy = UseOnlyComputationalLR
    , morFuel = 10
    }

buildInj
  :: Text
  -> Doctrine
  -> Doctrine
  -> AttrSortRenameMap
  -> TypeRenameMap
  -> TypePermMap
  -> M.Map (ModeName, GenName) GenName
  -> Either Text Morphism
buildInj name src tgt attrRen tyRen permRen genRen = do
  attrSortMap <- buildAttrSortMap src attrRen
  typeMap <- buildTypeMap src tyRen permRen
  genMap <- buildGenMap src tgt attrRen tyRen permRen genRen
  pure Morphism
    { morName = name
    , morSrc = src
    , morTgt = tgt
    , morIsCoercion = True
    , morModeMap = identityModeMap src
    , morModMap = identityModMap src
    , morAttrSortMap = attrSortMap
    , morTypeMap = typeMap
    , morGenMap = genMap
    , morIxFunMap = M.empty
    , morPolicy = UseOnlyComputationalLR
    , morFuel = 10
    }

buildAttrSortMap :: Doctrine -> AttrSortRenameMap -> Either Text (M.Map AttrSort AttrSort)
buildAttrSortMap doc renames =
  foldM add M.empty (M.keys (dAttrSorts doc))
  where
    add mp srcSort =
      let tgtSort = M.findWithDefault srcSort srcSort renames
      in Right (M.insert srcSort tgtSort mp)

buildTypeMap :: Doctrine -> TypeRenameMap -> TypePermMap -> Either Text (M.Map TypeRef TypeTemplate)
buildTypeMap doc renames permRen =
  foldM add M.empty (allTypes doc)
  where
    add mp (ref, sig) = do
      let ref' = M.findWithDefault ref ref renames
      let mPerm = M.lookup ref permRen
      if ref' == ref && mPerm == Nothing
        then Right mp
        else do
          tmpl <- renameTemplate ref' mPerm (tsParams sig)
          Right (M.insert ref tmpl mp)
    renameTemplate tgtRef mPerm params = do
      tmplParams <- mapM mkParam (zip [0 :: Int ..] params)
      args0 <- mapM toArg tmplParams
      args <- case mPerm of
        Nothing -> Right args0
        Just perm -> applyPerm perm args0
      pure (TypeTemplate tmplParams (TCon tgtRef args))

    mkParam (i, param) =
      case param of
        PS_Ty mode ->
          Right (TPType TyVar { tvName = "a" <> T.pack (show i), tvMode = mode })
        PS_Ix sortTy -> do
          sortTy' <- renameTypeExpr renames permRen sortTy
          Right (TPIx IxVar { ixvName = "i" <> T.pack (show i), ixvSort = sortTy', ixvScope = 0 })

    toArg param =
      case param of
        TPType v -> Right (TAType (TVar v))
        TPIx v -> Right (TAIndex (IXVar v))

buildGenMap
  :: Doctrine
  -> Doctrine
  -> AttrSortRenameMap
  -> TypeRenameMap
  -> TypePermMap
  -> M.Map (ModeName, GenName) GenName
  -> Either Text (M.Map (ModeName, GenName) Diagram)
buildGenMap src tgt attrRen tyRen permRen genRen =
  fmap M.fromList (mapM build (allGens src))
  where
    build (mode, gen) = do
      let genName = gdName gen
      let genName' = M.findWithDefault genName (mode, genName) genRen
      dom <- mapM (renameTypeExpr tyRen permRen) (gdPlainDom gen)
      cod <- mapM (renameTypeExpr tyRen permRen) (gdCod gen)
      _ <- ensureGenExists tgt mode genName'
      let attrs =
            M.fromList
              [ (fieldName, ATVar (AttrVar fieldName (M.findWithDefault sortName sortName attrRen)))
              | (fieldName, sortName) <- gdAttrs gen
              ]
      d <- genDWithAttrs mode dom cod genName' attrs
      pure ((mode, genName), d)

checkGenerated :: Text -> Morphism -> Either Text ()
checkGenerated label mor =
  case checkMorphism mor of
    Left err -> Left ("poly pushout generated morphism " <> label <> " invalid: " <> err)
    Right () -> Right ()

allTypes :: Doctrine -> [(TypeRef, TypeSig)]
allTypes doc =
  [ (TypeRef mode name, sig)
  | (mode, table) <- M.toList (dTypes doc)
  , (name, sig) <- M.toList table
  ]

allGens :: Doctrine -> [(ModeName, GenDecl)]
allGens doc =
  [ (mode, gen)
  | (mode, table) <- M.toList (dGens doc)
  , gen <- M.elems table
  ]
