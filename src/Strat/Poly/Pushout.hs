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
import Strat.Poly.Graph (Edge(..), EdgePayload(..), canonicalizeDiagram, diagramPortIds)
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
  let renameTypesB = M.fromList [ ((m, img), src) | ((m, src), img) <- M.toList typeMapF ]
  let renameTypesC = M.fromList [ ((m, img), src) | ((m, src), img) <- M.toList typeMapG ]
  let renameGensB = M.fromList [ ((m, img), src) | ((m, src), img) <- M.toList genMapF ]
  let renameGensC = M.fromList [ ((m, img), src) | ((m, src), img) <- M.toList genMapG ]
  b' <- renameDoctrine renameTypesB renameGensB (morTgt f)
  c' <- renameDoctrine renameTypesC renameGensC (morTgt g)
  merged <- mergeDoctrineList [morSrc f, b', c']
  let pres = merged { dName = name }
  glue <- buildGlue name (morSrc f) pres
  inl <- buildInj (name <> ".inl") (morTgt f) pres renameTypesB renameGensB
  inr <- buildInj (name <> ".inr") (morTgt g) pres renameTypesC renameGensC
  checkGenerated (morName glue) glue
  checkGenerated (morName inl) inl
  checkGenerated (morName inr) inr
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
  canon <- canonicalizeDiagram diag
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

renameDoctrine :: M.Map (ModeName, TypeName) TypeName -> M.Map (ModeName, GenName) GenName -> Doctrine -> Either Text Doctrine
renameDoctrine tyRen genRen doc = do
  types' <- M.traverseWithKey renameTypeTable (dTypes doc)
  gens' <- M.traverseWithKey renameGenTable (dGens doc)
  let cells' = map (renameCell tyRen genRen) (dCells2 doc)
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
          let gen' = gen { gdName = name' }
          case M.lookup name' mp of
            Nothing -> Right (M.insert name' gen' mp)
            Just existing | existing == gen' -> Right mp
            _ -> Left "poly pushout: generator name collision"

renameCell :: M.Map (ModeName, TypeName) TypeName -> M.Map (ModeName, GenName) GenName -> Cell2 -> Cell2
renameCell tyRen genRen cell =
  cell
    { c2LHS = renameDiagram tyRen genRen (c2LHS cell)
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
      pure a { dTypes = types, dGens = gens, dCells2 = dCells2 a <> dCells2 b }
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

buildGlue :: Text -> Doctrine -> Doctrine -> Either Text Morphism
buildGlue name src tgt = do
  genMap <- buildGenMap src tgt M.empty M.empty
  pure Morphism
    { morName = name <> ".glue"
    , morSrc = src
    , morTgt = tgt
    , morTypeMap = M.empty
    , morGenMap = genMap
    , morPolicy = UseAllOriented
    , morFuel = 50
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
    , morPolicy = UseAllOriented
    , morFuel = 50
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
