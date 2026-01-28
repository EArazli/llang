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
import Strat.Kernel.RewriteSystem (RewritePolicy(..))
import Strat.Poly.Doctrine
import Strat.Poly.Morphism
import Strat.Poly.ModeTheory (ModeName)
import Strat.Poly.TypeExpr
import Strat.Poly.UnifyTy (applySubstCtx)
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Diagram (Diagram(..), applySubstDiagram, genD)
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
  (typeMapF, permMapF) <- requireTypeRenameMap f
  (typeMapG, permMapG) <- requireTypeRenameMap g
  genMapF <- requireGenRenameMap f
  genMapG <- requireGenRenameMap g
  ensureInjective "type" (M.elems typeMapF)
  ensureInjective "type" (M.elems typeMapG)
  ensureInjective "gen" (M.elems genMapF)
  ensureInjective "gen" (M.elems genMapG)
  let renameTypesB0 = M.fromList [ ((m, img), src) | ((m, src), img) <- M.toList typeMapF ]
  let renameTypesC0 = M.fromList [ ((m, img), src) | ((m, src), img) <- M.toList typeMapG ]
  let permTypesB0 = permMapF
  let permTypesC0 = permMapG
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
  b' <- renameDoctrine renameTypesB permTypesB0 renameGensB renameCellsB (morTgt f)
  c' <- renameDoctrine renameTypesC permTypesC0 renameGensC renameCellsC (morTgt g)
  merged <- mergeDoctrineList [morSrc f, b', c']
  let pres = merged { dName = name }
  glue <- buildGlue name (morSrc f) pres
  inl <- buildInj (name <> ".inl") (morTgt f) pres renameTypesB permTypesB0 renameGensB
  inr <- buildInj (name <> ".inr") (morTgt g) pres renameTypesC permTypesC0 renameGensC
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

requireTypeRenameMap :: Morphism -> Either Text (M.Map (ModeName, TypeName) TypeName, M.Map (ModeName, TypeName) [Int])
requireTypeRenameMap mor = do
  let src = morSrc mor
  let types = allTypes src
  entries <- mapM (typeImage mor) types
  let typeMap = M.fromList [ ((mode, name), tgtName) | (mode, name, tgtName, _) <- entries ]
  permMap <- foldM insertPerm M.empty entries
  pure (typeMap, permMap)
  where
    typeImage m (mode, name, arity) = do
      (tgtName, mPerm) <- case M.lookup (mode, name) (morTypeMap m) of
        Nothing -> Right (name, Nothing)
        Just tmpl -> templateTarget tmpl arity
      ensureTypeExists (morTgt m) mode tgtName arity
      pure (mode, name, tgtName, mPerm)
    insertPerm mp (mode, _name, tgtName, mPerm) =
      case mPerm of
        Nothing -> Right mp
        Just perm ->
          let key = (mode, tgtName)
          in case M.lookup key mp of
              Nothing -> Right (M.insert key perm mp)
              Just existing
                | existing == perm -> Right mp
                | otherwise -> Left "poly pushout: inconsistent type permutation"
    templateTarget tmpl arity =
      case ttBody tmpl of
        TCon t params
          | length (ttParams tmpl) == arity
          , length params == arity
          , all isVar params
          , let vars = [ v | TVar v <- params ]
          , length vars == length (S.fromList vars)
          , S.fromList vars == S.fromList (ttParams tmpl)
          -> do
            let indexMap = M.fromList (zip (ttParams tmpl) [0..])
            perm <- mapM (lookupIndex indexMap) vars
            inv <- invertPermutation arity perm
            let ident = [0 .. arity - 1]
            let inv' = if perm == ident then Nothing else Just inv
            pure (t, inv')
        _ -> Left "poly pushout requires renaming type maps"
    lookupIndex mp v =
      case M.lookup v mp of
        Nothing -> Left "poly pushout requires renaming type maps"
        Just idx -> Right idx
    isVar (TVar _) = True
    isVar _ = False

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

renameDoctrine :: M.Map (ModeName, TypeName) TypeName -> M.Map (ModeName, TypeName) [Int] -> M.Map (ModeName, GenName) GenName -> M.Map (ModeName, Text) Text -> Doctrine -> Either Text Doctrine
renameDoctrine tyRen permRen genRen cellRen doc = do
  types' <- M.traverseWithKey renameTypeTable (dTypes doc)
  gens' <- M.traverseWithKey renameGenTable (dGens doc)
  cells' <- mapM (renameCell tyRen permRen genRen cellRen) (dCells2 doc)
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
          dom' <- mapM (renameTypeExpr mode tyRen permRen) (gdDom gen)
          cod' <- mapM (renameTypeExpr mode tyRen permRen) (gdCod gen)
          let gen' = gen { gdName = name', gdDom = dom', gdCod = cod' }
          case M.lookup name' mp of
            Nothing -> Right (M.insert name' gen' mp)
            Just existing | existing == gen' -> Right mp
            _ -> Left "poly pushout: generator name collision"

renameCell :: M.Map (ModeName, TypeName) TypeName -> M.Map (ModeName, TypeName) [Int] -> M.Map (ModeName, GenName) GenName -> M.Map (ModeName, Text) Text -> Cell2 -> Either Text Cell2
renameCell tyRen permRen genRen cellRen cell = do
  let mode = dMode (c2LHS cell)
  let name' = M.findWithDefault (c2Name cell) (mode, c2Name cell) cellRen
  lhs' <- renameDiagram tyRen permRen genRen (c2LHS cell)
  rhs' <- renameDiagram tyRen permRen genRen (c2RHS cell)
  pure cell
    { c2Name = name'
    , c2LHS = lhs'
    , c2RHS = rhs'
    }

renameDiagram :: M.Map (ModeName, TypeName) TypeName -> M.Map (ModeName, TypeName) [Int] -> M.Map (ModeName, GenName) GenName -> Diagram -> Either Text Diagram
renameDiagram tyRen permRen genRen diag = do
  let mode = dMode diag
  dPortTy' <- traverse (renameTypeExpr mode tyRen permRen) (dPortTy diag)
  dEdges' <- traverse (renameEdge mode) (dEdges diag)
  pure diag { dPortTy = dPortTy', dEdges = dEdges' }
  where
    renameEdge mode edge =
      case ePayload edge of
        PGen gen ->
          let gen' = M.findWithDefault gen (mode, gen) genRen
          in Right edge { ePayload = PGen gen' }
        PBox name inner -> do
          inner' <- renameDiagram tyRen permRen genRen inner
          pure edge { ePayload = PBox name inner' }

renameTypeExpr :: ModeName -> M.Map (ModeName, TypeName) TypeName -> M.Map (ModeName, TypeName) [Int] -> TypeExpr -> Either Text TypeExpr
renameTypeExpr mode ren permRen ty =
  case ty of
    TVar v -> Right (TVar v)
    TCon name args -> do
      args' <- mapM (renameTypeExpr mode ren permRen) args
      let name' = M.findWithDefault name (mode, name) ren
      case M.lookup (mode, name) permRen of
        Nothing -> Right (TCon name' args')
        Just perm -> do
          args'' <- applyPerm perm args'
          Right (TCon name' args'')

applyPerm :: [Int] -> [a] -> Either Text [a]
applyPerm perm args
  | length perm /= n = Left "poly pushout: type permutation arity mismatch"
  | any outOfRange perm = Left "poly pushout: type permutation index out of range"
  | length (S.fromList perm) /= n = Left "poly pushout: type permutation is not a bijection"
  | otherwise = Right [ args !! i | i <- perm ]
  where
    n = length args
    outOfRange i = i < 0 || i >= n

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
            Just g | genDeclAlphaEq g gen -> Right mp
            _ -> Left "poly pushout: generator conflict"

mergeCells :: [Cell2] -> [Cell2] -> Either Text [Cell2]
mergeCells left right =
  foldl insertCell (Right []) (left <> right)
  where
    insertCell acc cell = do
      cells <- acc
      match <- findMatch cell cells
      case match of
        Nothing -> Right (cells <> [cell])
        Just existing ->
          if c2Class existing == c2Class cell && c2Orient existing == c2Orient cell
            then Right cells
            else Left ("poly pushout: cell conflict (" <> c2Name existing <> ", " <> c2Name cell <> ")")

    findMatch cell cells = do
      matches <- filterM (cellBodyEq cell) cells
      case matches of
        [] -> Right Nothing
        (c:_) -> Right (Just c)

    cellBodyEq a b = do
      if dMode (c2LHS a) /= dMode (c2LHS b)
        then Right False
        else if length (c2TyVars a) /= length (c2TyVars b)
          then Right False
          else do
            b' <- alphaRenameCellTo (c2TyVars b) (c2TyVars a) b
            okL <- isoOrFalse (c2LHS a) (c2LHS b')
            okR <- isoOrFalse (c2RHS a) (c2RHS b')
            pure (okL && okR)

    isoOrFalse d1 d2 =
      case diagramIsoEq d1 d2 of
        Left _ -> Right False
        Right ok -> Right ok

genDeclAlphaEq :: GenDecl -> GenDecl -> Bool
genDeclAlphaEq g1 g2 =
  gdMode g1 == gdMode g2
    && gdName g1 == gdName g2
    && length (gdTyVars g1) == length (gdTyVars g2)
    && let subst = M.fromList (zip (gdTyVars g2) (map TVar (gdTyVars g1)))
           dom2 = applySubstCtx subst (gdDom g2)
           cod2 = applySubstCtx subst (gdCod g2)
       in dom2 == gdDom g1 && cod2 == gdCod g1

alphaRenameCellTo :: [TyVar] -> [TyVar] -> Cell2 -> Either Text Cell2
alphaRenameCellTo from to cell
  | length from /= length to = Left "poly pushout: alpha rename arity mismatch"
  | otherwise =
      let subst = M.fromList (zip from (map TVar to))
          lhs' = applySubstDiagram subst (c2LHS cell)
          rhs' = applySubstDiagram subst (c2RHS cell)
      in Right cell { c2TyVars = to, c2LHS = lhs', c2RHS = rhs' }

buildGlue :: Text -> Doctrine -> Doctrine -> Either Text Morphism
buildGlue name src tgt = do
  genMap <- buildGenMap src tgt M.empty M.empty M.empty
  pure Morphism
    { morName = name <> ".glue"
    , morSrc = src
    , morTgt = tgt
    , morTypeMap = M.empty
    , morGenMap = genMap
    , morPolicy = UseOnlyComputationalLR
    , morFuel = 10
    }

buildInj :: Text -> Doctrine -> Doctrine -> M.Map (ModeName, TypeName) TypeName -> M.Map (ModeName, TypeName) [Int] -> M.Map (ModeName, GenName) GenName -> Either Text Morphism
buildInj name src tgt tyRen permRen genRen = do
  typeMap <- buildTypeMap src tyRen permRen
  genMap <- buildGenMap src tgt tyRen permRen genRen
  pure Morphism
    { morName = name
    , morSrc = src
    , morTgt = tgt
    , morTypeMap = typeMap
    , morGenMap = genMap
    , morPolicy = UseOnlyComputationalLR
    , morFuel = 10
    }

buildTypeMap :: Doctrine -> M.Map (ModeName, TypeName) TypeName -> M.Map (ModeName, TypeName) [Int] -> Either Text (M.Map (ModeName, TypeName) TypeTemplate)
buildTypeMap doc renames permRen =
  foldM add M.empty (allTypes doc)
  where
    renameType mode name = M.findWithDefault name (mode, name) renames
    add mp (mode, name, arity) = do
      let name' = renameType mode name
      let mPerm = M.lookup (mode, name) permRen
      if name' == name && mPerm == Nothing
        then Right mp
        else do
          tmpl <- renameTemplate name' mPerm arity
          Right (M.insert (mode, name) tmpl mp)
    renameTemplate tgtName mPerm arity = do
      let vars = [ TyVar ("a" <> T.pack (show i)) | i <- [0..arity-1] ]
      vars' <- case mPerm of
        Nothing -> Right vars
        Just perm -> applyPerm perm vars
      pure (TypeTemplate vars (TCon tgtName (map TVar vars')))

buildGenMap :: Doctrine -> Doctrine -> M.Map (ModeName, TypeName) TypeName -> M.Map (ModeName, TypeName) [Int] -> M.Map (ModeName, GenName) GenName -> Either Text (M.Map (ModeName, GenName) Diagram)
buildGenMap src tgt tyRen permRen genRen =
  fmap M.fromList (mapM build (allGens src))
  where
    build (mode, gen) = do
      let genName = gdName gen
      let genName' = M.findWithDefault genName (mode, genName) genRen
      dom <- mapM (renameTypeExpr mode tyRen permRen) (gdDom gen)
      cod <- mapM (renameTypeExpr mode tyRen permRen) (gdCod gen)
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
