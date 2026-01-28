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
import Strat.Kernel.RewriteSystem (RewritePolicy(..))
import Strat.Poly.Doctrine
import Strat.Poly.Morphism
import Strat.Poly.ModeTheory (ModeName)
import Strat.Poly.TypeExpr
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Diagram
import Strat.Poly.Graph (Edge(..), EdgePayload(..), renumberDiagram, diagramPortIds, diagramIsoEq)
import Strat.Poly.Cell2 (Cell2(..))


data PolyPushoutResult = PolyPushoutResult
  { poDoctrine :: Doctrine
  , poInl :: Morphism
  , poInr :: Morphism
  , poGlue :: Morphism
  } deriving (Eq, Show)

computePolyPushout :: Text -> Morphism -> Morphism -> Either Text PolyPushoutResult
computePolyPushout name f g = do
  ensureSameSource
  ensureSameModes (morSrc f) (morTgt f)
  ensureSameModes (morSrc g) (morTgt g)
  typeMapF <- requireTypeRenameMap f
  typeMapG <- requireTypeRenameMap g
  genMapF <- requireGenRenameMap f
  genMapG <- requireGenRenameMap g
  ensureInjective "type" (M.elems typeMapF)
  ensureInjective "type" (M.elems typeMapG)
  ensureInjective "gen" (M.elems genMapF)
  ensureInjective "gen" (M.elems genMapG)
  let renameTypesB0 = M.fromList [ ((m, img), src) | ((m, src), img) <- M.toList typeMapF ]
  let renameTypesC0 = M.fromList [ ((m, img), src) | ((m, src), img) <- M.toList typeMapG ]
  let renameGensB0 = M.fromList [ ((m, img), src) | ((m, src), img) <- M.toList genMapF ]
  let renameGensC0 = M.fromList [ ((m, img), src) | ((m, src), img) <- M.toList genMapG ]
  let prefixB = sanitizePrefix (dName (morTgt f)) <> "_inl"
  let prefixC = sanitizePrefix (dName (morTgt g)) <> "_inr"
  let renameTypesB = M.union renameTypesB0 (disjointTypeRenames prefixB (morSrc f) renameTypesB0 (morTgt f))
  let renameTypesC = M.union renameTypesC0 (disjointTypeRenames prefixC (morSrc f) renameTypesC0 (morTgt g))
  let renameGensB = M.union renameGensB0 (disjointGenRenames prefixB (morSrc f) renameGensB0 (morTgt f))
  let renameGensC = M.union renameGensC0 (disjointGenRenames prefixC (morSrc f) renameGensC0 (morTgt g))
  let renameCellsB = disjointCellRenames prefixB (morSrc f) (morTgt f)
  let renameCellsC = disjointCellRenames prefixC (morSrc f) (morTgt g)
  b' <- renameDoctrine renameTypesB renameGensB renameCellsB (morTgt f)
  c' <- renameDoctrine renameTypesC renameGensC renameCellsC (morTgt g)
  merged <- mergeDoctrineList [morSrc f, b', c']
  let pres = merged { dName = name }
  glue <- buildGlue name (morSrc f) pres
  inl <- buildInj (name <> ".inl") (morTgt f) pres renameTypesB renameGensB
  inr <- buildInj (name <> ".inr") (morTgt g) pres renameTypesC renameGensC
  checkGenerated "glue" glue
  checkGenerated "inl" inl
  checkGenerated "inr" inr
  pure PolyPushoutResult { poDoctrine = pres, poInl = inl, poInr = inr, poGlue = glue }
  where
    ensureSameSource =
      if morSrc f == morSrc g
        then Right ()
        else Left "poly pushout requires morphisms with the same source"

computePolyCoproduct :: Text -> Doctrine -> Doctrine -> Either Text PolyPushoutResult
computePolyCoproduct name a b = do
  ensureSameModes a b
  let empty = Doctrine
        { dName = "Empty"
        , dModes = dModes a
        , dTypes = M.empty
        , dGens = M.empty
        , dCells2 = []
        }
  let morA = Morphism
        { morName = "coproduct.inl0"
        , morSrc = empty
        , morTgt = a
        , morTypeMap = M.empty
        , morGenMap = M.empty
        , morPolicy = UseAllOriented
        , morFuel = 50
        }
  let morB = Morphism
        { morName = "coproduct.inr0"
        , morSrc = empty
        , morTgt = b
        , morTypeMap = M.empty
        , morGenMap = M.empty
        , morPolicy = UseAllOriented
        , morFuel = 50
        }
  computePolyPushout name morA morB

ensureSameModes :: Doctrine -> Doctrine -> Either Text ()
ensureSameModes a b =
  if dModes a == dModes b
    then Right ()
    else Left "poly pushout requires identical mode theories"

requireTypeRenameMap :: Morphism -> Either Text (M.Map (ModeName, TypeName) TypeName)
requireTypeRenameMap mor = do
  let src = morSrc mor
  let types = allTypes src
  fmap M.fromList (mapM (typeImage mor) types)
  where
    typeImage m (mode, name, arity) = do
      tgtName <- case M.lookup (mode, name) (morTypeMap m) of
        Nothing -> Right name
        Just tmpl -> do
          case tmpl of
            TCon t params
              | length params == arity && all isVar params && distinct params -> Right t
              | otherwise -> Left "poly pushout requires renaming type maps"
            _ -> Left "poly pushout requires renaming type maps"
      ensureTypeExists (morTgt m) mode tgtName arity
      pure ((mode, name), tgtName)
    isVar (TVar _) = True
    isVar _ = False
    distinct params =
      let vars = [ v | TVar v <- params ]
      in length vars == length (S.fromList vars)

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
          imgName <- singleGenName d
          ensureGenExists (morTgt m) mode imgName
          Right imgName
      pure ((mode, gdName gen), img)

singleGenName :: Diagram -> Either Text GenName
singleGenName diag = do
  canon <- renumberDiagram diag
  case IM.elems (dEdges canon) of
    [edge] -> do
      let boundary = dIn canon <> dOut canon
      let edgePorts = eIns edge <> eOuts edge
      let allPorts = diagramPortIds canon
      case ePayload edge of
        PGen g ->
          if boundary == edgePorts && length allPorts == length boundary
            then Right g
            else Left "poly pushout requires generator mappings to be a single generator"
        _ -> Left "poly pushout requires generator mappings to be a single generator"
    _ -> Left "poly pushout requires generator mappings to be a single generator"

ensureTypeExists :: Doctrine -> ModeName -> TypeName -> Int -> Either Text ()
ensureTypeExists doc mode name arity =
  case M.lookup mode (dTypes doc) >>= M.lookup name of
    Nothing -> Left "poly pushout: target type missing"
    Just a | a == arity -> Right ()
    _ -> Left "poly pushout: target type arity mismatch"

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

disjointTypeRenames :: Text -> Doctrine -> M.Map (ModeName, TypeName) TypeName -> Doctrine -> M.Map (ModeName, TypeName) TypeName
disjointTypeRenames prefix src interfaceRen tgt =
  foldl add M.empty (M.toList (dTypes tgt))
  where
    srcNames = namesByMode [ (mode, name) | (mode, name, _) <- allTypes src ]
    add acc (mode, table) =
      let reserved = M.findWithDefault S.empty mode srcNames
      in M.union acc (renameMode mode reserved (M.keys table))
    renameMode mode reserved names =
      let (_, mp) = foldl (step mode) (reserved, M.empty) names
      in mp
    step mode (used, mp) name =
      let key = (mode, name)
      in if M.member key interfaceRen
        then (used, mp)
        else
          let (name', used') = freshTypeName prefix name used
          in (used', M.insert key name' mp)

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

renameDoctrine :: M.Map (ModeName, TypeName) TypeName -> M.Map (ModeName, GenName) GenName -> M.Map (ModeName, Text) Text -> Doctrine -> Either Text Doctrine
renameDoctrine tyRen genRen cellRen doc = do
  types' <- M.traverseWithKey renameTypeTable (dTypes doc)
  gens' <- M.traverseWithKey renameGenTable (dGens doc)
  let cells' = map (renameCell tyRen genRen cellRen) (dCells2 doc)
  pure doc { dTypes = types', dGens = gens', dCells2 = cells' }
  where
    renameTypeTable mode table =
      foldl add (Right M.empty) (M.toList table)
      where
        add acc (name, arity) = do
          mp <- acc
          let name' = M.findWithDefault name (mode, name) tyRen
          case M.lookup name' mp of
            Nothing -> Right (M.insert name' arity mp)
            Just a | a == arity -> Right mp
            _ -> Left "poly pushout: type name collision"
    renameGenTable mode table =
      foldl add (Right M.empty) (M.elems table)
      where
        add acc gen = do
          mp <- acc
          let name' = M.findWithDefault (gdName gen) (mode, gdName gen) genRen
          let dom' = map (renameTypeExpr mode tyRen) (gdDom gen)
          let cod' = map (renameTypeExpr mode tyRen) (gdCod gen)
          let gen' = gen { gdName = name', gdDom = dom', gdCod = cod' }
          case M.lookup name' mp of
            Nothing -> Right (M.insert name' gen' mp)
            Just existing | existing == gen' -> Right mp
            _ -> Left "poly pushout: generator name collision"

renameCell :: M.Map (ModeName, TypeName) TypeName -> M.Map (ModeName, GenName) GenName -> M.Map (ModeName, Text) Text -> Cell2 -> Cell2
renameCell tyRen genRen cellRen cell =
  let mode = dMode (c2LHS cell)
      name' = M.findWithDefault (c2Name cell) (mode, c2Name cell) cellRen
  in cell
    { c2Name = name'
    , c2LHS = renameDiagram tyRen genRen (c2LHS cell)
    , c2RHS = renameDiagram tyRen genRen (c2RHS cell)
    }

renameDiagram :: M.Map (ModeName, TypeName) TypeName -> M.Map (ModeName, GenName) GenName -> Diagram -> Diagram
renameDiagram tyRen genRen diag =
  let mode = dMode diag
      dPortTy' = IM.map (renameTypeExpr mode tyRen) (dPortTy diag)
      dEdges' = IM.map (renameEdge mode) (dEdges diag)
  in diag { dPortTy = dPortTy', dEdges = dEdges' }
  where
    renameEdge mode edge =
      case ePayload edge of
        PGen gen ->
          let gen' = M.findWithDefault gen (mode, gen) genRen
          in edge { ePayload = PGen gen' }
        PBox name inner ->
          let inner' = renameDiagram tyRen genRen inner
          in edge { ePayload = PBox name inner' }

renameTypeExpr :: ModeName -> M.Map (ModeName, TypeName) TypeName -> TypeExpr -> TypeExpr
renameTypeExpr mode ren ty =
  case ty of
    TVar v -> TVar v
    TCon name args ->
      let name' = M.findWithDefault name (mode, name) ren
      in TCon name' (map (renameTypeExpr mode ren) args)

mergeDoctrineList :: [Doctrine] -> Either Text Doctrine
mergeDoctrineList [] = Left "poly pushout: no doctrines to merge"
mergeDoctrineList (d:ds) = foldl merge (Right d) ds
  where
    merge acc next = do
      base <- acc
      mergeDoctrine base next

mergeDoctrine :: Doctrine -> Doctrine -> Either Text Doctrine
mergeDoctrine a b = do
  if dModes a /= dModes b
    then Left "poly pushout: mode mismatch"
    else do
      types <- mergeTypeTables (dTypes a) (dTypes b)
      gens <- mergeGenTables (dGens a) (dGens b)
      cells <- mergeCells (dCells2 a) (dCells2 b)
      pure a { dTypes = types, dGens = gens, dCells2 = cells }
  where
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
        add acc (name, arity) = do
          mp <- acc
          case M.lookup name mp of
            Nothing -> Right (M.insert name arity mp)
            Just a | a == arity -> Right mp
            _ -> Left "poly pushout: type arity conflict"
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
            Just g | g == gen -> Right mp
            _ -> Left "poly pushout: generator conflict"

mergeCells :: [Cell2] -> [Cell2] -> Either Text [Cell2]
mergeCells left right = do
  (mp, order) <- foldl insertCell (Right (M.empty, [])) left
  (mp', order') <- foldl insertCell (Right (mp, order)) right
  pure [ mp' M.! key | key <- order' ]
  where
    insertCell acc cell = do
      (mp, order) <- acc
      let key = cellKey cell
      case M.lookup key mp of
        Nothing -> Right (M.insert key cell mp, order <> [key])
        Just existing -> do
          ensureCompatible existing cell
          Right (mp, order)
    cellKey cell = (dMode (c2LHS cell), c2Name cell)
    ensureCompatible a b =
      if c2Class a /= c2Class b || c2Orient a /= c2Orient b
        then Left "poly pushout: cell conflict"
        else do
          okL <- diagramIsoEq (c2LHS a) (c2LHS b)
          okR <- diagramIsoEq (c2RHS a) (c2RHS b)
          if okL && okR
            then Right ()
            else Left "poly pushout: cell conflict"

buildGlue :: Text -> Doctrine -> Doctrine -> Either Text Morphism
buildGlue name src tgt = do
  genMap <- buildGenMap src tgt M.empty M.empty
  pure Morphism
    { morName = name <> ".glue"
    , morSrc = src
    , morTgt = tgt
    , morTypeMap = M.empty
    , morGenMap = genMap
    , morPolicy = UseOnlyComputationalLR
    , morFuel = 10
    }

buildInj :: Text -> Doctrine -> Doctrine -> M.Map (ModeName, TypeName) TypeName -> M.Map (ModeName, GenName) GenName -> Either Text Morphism
buildInj name src tgt tyRen genRen = do
  let typeMap = buildTypeMap src tyRen
  genMap <- buildGenMap src tgt tyRen genRen
  pure Morphism
    { morName = name
    , morSrc = src
    , morTgt = tgt
    , morTypeMap = typeMap
    , morGenMap = genMap
    , morPolicy = UseOnlyComputationalLR
    , morFuel = 10
    }

buildTypeMap :: Doctrine -> M.Map (ModeName, TypeName) TypeName -> M.Map (ModeName, TypeName) TypeExpr
buildTypeMap doc renames =
  M.fromList
    [ ((mode, name), renameTemplate (renameType mode name) arity)
    | (mode, name, arity) <- allTypes doc
    , let name' = renameType mode name
    , name' /= name
    ]
  where
    renameType mode name = M.findWithDefault name (mode, name) renames
    renameTemplate tgtName arity =
      let vars = [ TyVar ("a" <> T.pack (show i)) | i <- [0..arity-1] ]
      in TCon tgtName (map TVar vars)

buildGenMap :: Doctrine -> Doctrine -> M.Map (ModeName, TypeName) TypeName -> M.Map (ModeName, GenName) GenName -> Either Text (M.Map (ModeName, GenName) Diagram)
buildGenMap src tgt tyRen genRen =
  fmap M.fromList (mapM build (allGens src))
  where
    build (mode, gen) = do
      let genName = gdName gen
      let genName' = M.findWithDefault genName (mode, genName) genRen
      let dom = map (renameTypeExpr mode tyRen) (gdDom gen)
      let cod = map (renameTypeExpr mode tyRen) (gdCod gen)
      _ <- ensureGenExists tgt mode genName'
      d <- genD mode dom cod genName'
      pure ((mode, genName), d)

checkGenerated :: Text -> Morphism -> Either Text ()
checkGenerated label mor =
  case checkMorphism mor of
    Left err -> Left ("poly pushout generated morphism " <> label <> " invalid: " <> err)
    Right () -> Right ()

allTypes :: Doctrine -> [(ModeName, TypeName, Int)]
allTypes doc =
  [ (mode, name, arity)
  | (mode, table) <- M.toList (dTypes doc)
  , (name, arity) <- M.toList table
  ]

allGens :: Doctrine -> [(ModeName, GenDecl)]
allGens doc =
  [ (mode, gen)
  | (mode, table) <- M.toList (dGens doc)
  , gen <- M.elems table
  ]
