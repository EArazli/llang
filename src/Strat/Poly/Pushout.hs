{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Pushout
  ( PolyPushoutResult(..)
  , computePolyPushout
  , computePolyPushoutPreferRight
  , computePolyCoproduct
  , mkInclusionMorphism
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.IntMap.Strict as IM
import qualified Data.List as L
import Control.Monad (filterM, foldM)
import Data.Functor.Identity (runIdentity)
import Strat.Common.Rules (RewritePolicy(..))
import Strat.Common.Rules (RuleClass(..), Orientation(..))
import Strat.Poly.Doctrine
import Strat.Poly.Morphism
import Strat.Poly.ModeTheory
  ( ModeName(..)
  , ModeTheory(..)
  , ClassificationDecl(..)
  , CompDecl(..)
  , ModeInfo(..)
  , ModName(..)
  , ModDecl(..)
  , ModEqn(..)
  , ModExpr(..)
  , ModTransformName(..)
  , ModTransformDecl(..)
  , emptyModeTheory
  , checkWellFormed
  )
import Strat.Poly.Obj
import Strat.Poly.ObjClassifier (modeUniverseObj, modeClassifierMode)
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Attr
import Strat.Poly.Diagram (Diagram(..), genDWithAttrs, diagramDom, diagramCod)
import Strat.Poly.Graph (Edge(..), EdgePayload(..), BinderArg(..), BinderMetaVar(..), canonDiagramRaw, diagramPortIds)
import Strat.Poly.DiagramIso (diagramIsoEq)
import Strat.Poly.Cell2 (Cell2(..))
import Strat.Poly.Traversal (traverseDiagram)
import Strat.Poly.TermExpr (TermExpr(..))
import Strat.Poly.DefEq (termExprToDiagramChecked)
import Strat.Poly.TypeTheory (TypeParamSig(..))
import qualified Strat.Poly.DSL.AST as PolyAST


data PolyPushoutResult = PolyPushoutResult
  { poDoctrine :: Doctrine
  , poInl :: Morphism
  , poInr :: Morphism
  , poGlue :: Morphism
  } deriving (Eq, Show)

type TypeRenameMap = M.Map ObjRef ObjRef
type TypePermMap = M.Map ObjRef [Int]
type AttrSortRenameMap = M.Map AttrSort AttrSort
type GenRenameMap = M.Map (ModeName, GenName) GenName
type CellRenameMap = M.Map (ModeName, Text) Text
type OblRenameMap = M.Map Text Text
type TransformRenameMap = M.Map ModTransformName ModTransformName

mkTypeMetaVarForMode :: Doctrine -> ModeName -> Text -> Either Text TmVar
mkTypeMetaVarForMode doc ownerMode name = do
  universe <-
    case modeUniverseObj (dModes doc) ownerMode of
      Nothing ->
        Left
          ( "pushout: type metavariable `"
              <> name
              <> "@"
              <> renderMode ownerMode
              <> "` requires `mode "
              <> renderMode ownerMode
              <> " classifiedBy ... via ...;` with a declared universe"
          )
      Just u -> Right u
  pure
    TmVar
      { tmvName = name
      , tmvSort = universe
      , tmvScope = 0
      , tmvOwnerMode = Just ownerMode
      }
  where
    renderMode (ModeName n) = n

data ModePushout = ModePushout
  { mpoModeTheory :: ModeTheory
  , mpoInlModeRen :: M.Map ModeName ModeName
  , mpoInrModeRen :: M.Map ModeName ModeName
  , mpoInlModRen :: M.Map ModName ModName
  , mpoInrModRen :: M.Map ModName ModName
  }
  deriving (Eq, Show)

computePolyPushout :: Text -> Morphism -> Morphism -> Either Text PolyPushoutResult
computePolyPushout name f g = do
  ensureSameSource
  let src = morSrc f
  srcCtorTables <- deriveCtorTables src
  tgtFCtorTables <- deriveCtorTables (morTgt f)
  tgtGCtorTables <- deriveCtorTables (morTgt g)
  srcCtors <- allCtorsInTables src srcCtorTables
  let srcGens = allGensInTables src srcCtorTables
  modePushout <- pushoutModeTheoryPreferRight (sanitizePrefix name <> "_pushout") f g
  attrSortMapF <- requireAttrSortRenameMap f
  attrSortMapG <- requireAttrSortRenameMap g
  (typeMapF, permMapF) <- requireTypeRenameMap f
  (typeMapG, permMapG) <- requireTypeRenameMap g
  genMapF <- requireGenRenameMap f
  genMapG <- requireGenRenameMap g
  let srcAttrSorts = M.keys (dAttrSorts src)
  let srcTypeRefs = map fst srcCtors
  let srcGenKeys = [ (mode, gdName genDecl) | (mode, genDecl) <- srcGens ]
  attrRep <- classRepresentatives srcAttrSorts [groupByImage attrSortMapF, groupByImage attrSortMapG]
  typeRep <- classRepresentatives srcTypeRefs [groupByImage typeMapF, groupByImage typeMapG]
  genImgMapF <- generatorImageKeys f genMapF
  genImgMapG <- generatorImageKeys g genMapG
  genRep <- classRepresentatives srcGenKeys [groupByImage genImgMapF, groupByImage genImgMapG]
  ensureAttrSortClassCompat src attrRep
  ensureTypeClassCompat srcCtors typeRep
  ensureGenClassCompat srcGens genRep
  renameAttrSortsB0 <- imageToRepresentative "attrsort" attrSortMapF attrRep
  renameAttrSortsC0 <- imageToRepresentative "attrsort" attrSortMapG attrRep
  typeCanon <- canonicalTypeNamesFromRight typeRep typeMapG
  renameTypesB0 <- imageTypesToCanonicalNames "type" typeMapF typeRep typeCanon
  renameTypesC0 <- imageTypesToCanonicalNames "type" typeMapG typeRep typeCanon
  let permTypesB0 = permMapF
  let permTypesC0 = permMapG
  renameGensBWithModes <- imageToRepresentative "generator" genImgMapF genRep
  renameGensCWithModes <- imageToRepresentative "generator" genImgMapG genRep
  interfaceCellsB <- interfaceCellKeys f
  interfaceCellsC <- interfaceCellKeys g
  let renameGensB0 = M.map snd renameGensBWithModes
  let renameGensC0 = M.map snd renameGensCWithModes
  let prefixB = sanitizePrefix (dName (morTgt f)) <> "_inl"
  let prefixC = sanitizePrefix (dName (morTgt g)) <> "_inr"
  let renameAttrSortsB = M.union renameAttrSortsB0 (disjointAttrSortRenames prefixB src renameAttrSortsB0 (morTgt f))
  let renameAttrSortsC = M.union renameAttrSortsC0 (disjointAttrSortRenames prefixC src renameAttrSortsC0 (morTgt g))
  renameTypesBExtra <- disjointTypeRenames (mpoInlModeRen modePushout) prefixB renameTypesB0 tgtFCtorTables (morTgt f)
  renameTypesCExtra <- disjointTypeRenames (mpoInrModeRen modePushout) prefixC renameTypesC0 tgtGCtorTables (morTgt g)
  let renameTypesB = M.union renameTypesB0 renameTypesBExtra
  let renameTypesC = M.union renameTypesC0 renameTypesCExtra
  let renameGensB = M.union renameGensB0 (disjointGenRenames (mpoInlModeRen modePushout) prefixB renameGensB0 (morTgt f))
  let renameGensC = M.union renameGensC0 (disjointGenRenames (mpoInrModeRen modePushout) prefixC renameGensC0 (morTgt g))
  let renameCellsB = disjointCellRenames (mpoInlModeRen modePushout) prefixB interfaceCellsB (morTgt f)
  let renameCellsC = disjointCellRenames (mpoInrModeRen modePushout) prefixC interfaceCellsC (morTgt g)
  let renameOblsB = disjointObligationRenames prefixB src (morTgt f)
  let renameOblsC = disjointObligationRenames prefixC src (morTgt g)
  let renameTransformsB = disjointTransformRenames prefixB src (morTgt f)
  let renameTransformsC = disjointTransformRenames prefixC src (morTgt g)
  modeTransforms' <-
    mergeTransformsPreferRightWithWitness
      (sanitizePrefix name <> "_pushout")
      (mpoInlModeRen modePushout)
      (mpoInlModRen modePushout)
      renameGensB
      (mpoInrModeRen modePushout)
      (mpoInrModRen modePushout)
      renameGensC
      (dModes (morTgt f))
      (dModes (morTgt g))
  classFromRight <-
    renamedClassifiedByMap
      (mpoInrModeRen modePushout)
      (mpoInrModRen modePushout)
      renameTypesC
      permTypesC0
      renameGensC
      (dModes (morTgt g))
  classFromLeft <-
    renamedClassifiedByMap
      (mpoInlModeRen modePushout)
      (mpoInlModRen modePushout)
      renameTypesB
      permTypesB0
      renameGensB
      (dModes (morTgt f))
  let class0 = mergeClassifiedByPreferRight classFromRight classFromLeft
  let modeTheory' =
        (mpoModeTheory modePushout)
          { mtTransforms = modeTransforms'
          , mtClassifiedBy = class0
          }
  _ <- checkWellFormed modeTheory'
  let modePushout' = modePushout { mpoModeTheory = modeTheory' }
  b' <-
    renameDoctrine
      (mpoInlModeRen modePushout)
      (mpoInlModRen modePushout)
      renameAttrSortsB
      renameTypesB
      permTypesB0
      renameGensB
      renameCellsB
      renameOblsB
      renameTransformsB
      (morTgt f)
  c' <-
    renameDoctrine
      (mpoInrModeRen modePushout)
      (mpoInrModRen modePushout)
      renameAttrSortsC
      renameTypesC
      permTypesC0
      renameGensC
      renameCellsC
      renameOblsC
      renameTransformsC
      (morTgt g)
  let b'' = b' { dModes = mpoModeTheory modePushout' }
  let c'' = c' { dModes = mpoModeTheory modePushout' }
  merged <- mergeDoctrineList (mpoModeTheory modePushout') [b'', c'']
  let pres = merged { dName = name }
  inl <-
    buildInj
      (name <> ".inl")
      (morTgt f)
      pres
      (mpoInlModeRen modePushout)
      (mpoInlModRen modePushout)
      renameAttrSortsB
      renameTypesB
      permTypesB0
      renameGensB
  inr <-
    buildInj
      (name <> ".inr")
      (morTgt g)
      pres
      (mpoInrModeRen modePushout)
      (mpoInrModRen modePushout)
      renameAttrSortsC
      renameTypesC
      permTypesC0
      renameGensC
  glue0 <- composeMorphisms (name <> ".glue") g inr
  let glue = glue0 { morIsCoercion = True }
  checkGenerated "inl" inl
  checkGenerated "inr" inr
  pure PolyPushoutResult { poDoctrine = pres, poInl = inl, poInr = inr, poGlue = glue }
  where
    ensureSameSource =
      if morSrc f == morSrc g
        then Right ()
        else Left "poly pushout requires morphisms with the same source"

mkInclusionMorphism :: Text -> Doctrine -> Doctrine -> Either Text Morphism
mkInclusionMorphism name src tgt = do
  mor <- buildInj name src tgt M.empty M.empty M.empty M.empty M.empty M.empty
  checkGenerated "inclusion" mor
  pure mor

computePolyPushoutPreferRight :: Text -> Text -> Morphism -> Morphism -> Either Text PolyPushoutResult
computePolyPushoutPreferRight newName leftPrefix incl impl = do
  ensureSameSource
  let src = morSrc incl
  let body = morTgt incl
  let target = morTgt impl
  srcCtorTables <- deriveCtorTables src
  bodyCtorTables <- deriveCtorTables body
  targetCtorTables <- deriveCtorTables target
  modePushout <- pushoutModeTheoryPreferRight leftPrefix incl impl
  attrMapIncl <- requireAttrSortRenameMap incl
  attrMapImpl <- requireAttrSortRenameMap impl
  (typeMapIncl, permMapIncl) <- requireTypeRenameMap incl
  (typeMapImpl, permMapImpl) <- requireTypeRenameMap impl
  genMapIncl <- requireGenRenameMap incl
  genMapImpl <- requireGenRenameMap impl
  interfaceAttrRen <- mkInterfaceAttrSortRenameMap attrMapIncl attrMapImpl
  (interfaceTypeRen, interfacePermRen) <- mkInterfaceTypeRenameMap src srcCtorTables typeMapIncl permMapIncl typeMapImpl permMapImpl
  interfaceGenRen <- mkInterfaceGenRenameMap genMapIncl genMapImpl
  let prefix = sanitizePrefix leftPrefix
  let renameAttrSorts =
        M.union interfaceAttrRen
          (collisionAttrSortRenames prefix interfaceAttrRen target body)
  collisionTypeRen <-
    collisionTypeRenames
      (mpoInlModeRen modePushout)
      prefix
      interfaceTypeRen
      target
      targetCtorTables
      body
      bodyCtorTables
  let renameTypes =
        M.union interfaceTypeRen collisionTypeRen
  let renameGens =
        M.union interfaceGenRen
          (collisionGenRenames (mpoInlModeRen modePushout) prefix interfaceGenRen target body)
  let renameCells = collisionCellRenames (mpoInlModeRen modePushout) prefix src target body
  let renameObls = collisionObligationRenames prefix src target body
  let renameTransforms = collisionTransformRenames prefix src target body
  modeTransforms' <-
    mergeTransformsPreferRightWithWitness
      prefix
      (mpoInlModeRen modePushout)
      (mpoInlModRen modePushout)
      renameGens
      (mpoInrModeRen modePushout)
      (mpoInrModRen modePushout)
      M.empty
      (dModes body)
      (dModes target)
  classFromRight <-
    renamedClassifiedByMap
      (mpoInrModeRen modePushout)
      (mpoInrModRen modePushout)
      M.empty
      M.empty
      M.empty
      (dModes target)
  classFromLeft <-
    renamedClassifiedByMap
      (mpoInlModeRen modePushout)
      (mpoInlModRen modePushout)
      renameTypes
      interfacePermRen
      renameGens
      (dModes body)
  let class0 = mergeClassifiedByPreferRight classFromRight classFromLeft
  let modeTheory' =
        (mpoModeTheory modePushout)
          { mtTransforms = modeTransforms'
          , mtClassifiedBy = class0
          }
  _ <- checkWellFormed modeTheory'
  let modePushout' = modePushout { mpoModeTheory = modeTheory' }
  body' <-
    renameDoctrine
      (mpoInlModeRen modePushout)
      (mpoInlModRen modePushout)
      renameAttrSorts
      renameTypes
      interfacePermRen
      renameGens
      renameCells
      renameObls
      renameTransforms
      body
  target' <-
    renameDoctrine
      (mpoInrModeRen modePushout)
      (mpoInrModRen modePushout)
      M.empty
      M.empty
      M.empty
      M.empty
      M.empty
      M.empty
      M.empty
      target
  let body'' = body' { dModes = mpoModeTheory modePushout' }
  let target'' = target' { dModes = mpoModeTheory modePushout' }
  merged <- mergeDoctrine (mpoModeTheory modePushout') target'' body''
  let pres = merged { dName = newName }
  inr <-
    buildInj
      (newName <> ".inr")
      target
      pres
      (mpoInrModeRen modePushout)
      (mpoInrModRen modePushout)
      M.empty
      M.empty
      M.empty
      M.empty
  inl <-
    buildInj
      (newName <> ".inl")
      body
      pres
      (mpoInlModeRen modePushout)
      (mpoInlModRen modePushout)
      renameAttrSorts
      renameTypes
      interfacePermRen
      renameGens
  let glue =
        impl
          { morName = newName <> ".glue"
          , morTgt = pres
          , morIsCoercion = True
          }
  checkGenerated "inl" inl
  checkGenerated "inr" inr
  pure PolyPushoutResult { poDoctrine = pres, poInl = inl, poInr = inr, poGlue = glue }
  where
    ensureSameSource =
      if morSrc incl == morSrc impl
        then Right ()
        else Left "poly apply pushout requires morphisms with the same source"

pushoutModeTheoryPreferRight :: Text -> Morphism -> Morphism -> Either Text ModePushout
pushoutModeTheoryPreferRight prefixRaw leftMor rightMor = do
  let prefix = sanitizePrefix prefixRaw
  let mtSrc = dModes (morSrc leftMor)
  let mtLeft = dModes (morTgt leftMor)
  let mtRight = dModes (morTgt rightMor)
  let rightModes = M.keysSet (mtModes mtRight)
  interfaceModePairs <- mapM interfaceModeImage (M.keys (mtModes mtSrc))
  inlModeRen0 <- foldM addModeConstraint M.empty interfaceModePairs
  (inlModeRen, _usedModes) <- completeModeRenames prefix rightModes inlModeRen0 (M.keys (mtModes mtLeft))
  let inrModeRen = M.fromList [ (m, m) | m <- M.keys (mtModes mtRight) ]

  interfaceModPairs <- mapM interfaceModImage (M.keys (mtDecls mtSrc))
  inlModRenForced <- foldM addModConstraint M.empty interfaceModPairs
  let rightMods = M.keysSet (mtDecls mtRight)
  (inlModRen, _usedMods) <- completeModRenames prefix rightMods inlModRenForced (M.keys (mtDecls mtLeft))
  let inrModRen = M.fromList [ (m, m) | m <- M.keys (mtDecls mtRight) ]

  let modesFinal = buildModesFinal inlModeRen inrModeRen mtLeft mtRight
  declsFromRight <- renamedDeclMap inrModeRen inrModRen mtRight
  declsFromLeft <- renamedDeclMap inlModeRen inlModRen mtLeft
  decls0 <-
    mergeNamedMapsByEq
      "mode pushout: conflicting modality declarations"
      declsFromRight
      declsFromLeft
  liftsFromRight <- renamedLiftMap inrModeRen inrModRen mtRight
  liftsFromLeft <- renamedLiftMap inlModeRen inlModRen mtLeft
  lifts0 <-
    mergeNamedMapsByEq
      "mode pushout: conflicting classifier lifts"
      liftsFromRight
      liftsFromLeft
  let eqns0 =
        map (renameModEqn inrModeRen inrModRen) (mtEqns mtRight)
          <> map (renameModEqn inlModeRen inlModRen) (mtEqns mtLeft)
  (decls1, glueEqns) <-
    foldM
      (addGlueEqn prefix inlModeRen inlModRen inrModeRen inrModRen)
      (decls0, [])
      (M.keys (mtDecls mtSrc))
  transforms <-
    mergeTransformsPreferRightWithWitness
      prefix
      inlModeRen
      inlModRen
      M.empty
      inrModeRen
      inrModRen
      M.empty
      mtLeft
      mtRight
  let mtOut =
        ModeTheory
          { mtModes = modesFinal
          , mtDecls = decls1
          , mtEqns = eqns0 <> glueEqns
          , mtTransforms = transforms
          , mtClassifiedBy = M.empty
          , mtClassifierLifts = lifts0
          }
  _ <- checkWellFormed mtOut
  pure
    ModePushout
      { mpoModeTheory = mtOut
      , mpoInlModeRen = inlModeRen
      , mpoInrModeRen = inrModeRen
      , mpoInlModRen = inlModRen
      , mpoInrModRen = inrModRen
      }
  where
    interfaceModeImage srcMode = do
      leftMode <- lookupModeImage "left" leftMor srcMode
      rightMode <- lookupModeImage "right" rightMor srcMode
      pure (leftMode, rightMode)

    addModeConstraint acc (leftMode, rightMode) =
      case M.lookup leftMode acc of
        Nothing -> Right (M.insert leftMode rightMode acc)
        Just existing
          | existing == rightMode -> Right acc
          | otherwise ->
              Left
                ( "mode pushout: incompatible mode images for "
                    <> renderModeName leftMode
                )

    completeModeRenames pref rightSet forced leftModes =
      foldM step (forced, rightSet `S.union` S.fromList (M.elems forced)) leftModes
      where
        step (ren, used) mode =
          case M.lookup mode ren of
            Just _ -> Right (ren, used)
            Nothing ->
              if mode `S.member` used
                then
                  let (fresh, used') = freshModeName pref mode used
                  in Right (M.insert mode fresh ren, used')
                else
                  Right (M.insert mode mode ren, S.insert mode used)

    interfaceModImage srcMod = do
      leftExpr <- lookupModImage "left" leftMor srcMod
      rightExpr <- lookupModImage "right" rightMor srcMod
      pure (srcMod, leftExpr, rightExpr)

    addModConstraint acc (_srcMod, leftExpr, rightExpr) =
      case (mePath leftExpr, mePath rightExpr) of
        ([leftMod], [rightMod]) ->
          case M.lookup leftMod acc of
            Nothing -> Right (M.insert leftMod rightMod acc)
            Just existing
              | existing == rightMod -> Right acc
              | otherwise ->
                  Left
                    ( "mode pushout: incompatible modality images for "
                        <> renderModName leftMod
                    )
        _ -> Right acc

    completeModRenames pref rightSet forced leftMods =
      foldM step (forced, rightSet `S.union` S.fromList (M.elems forced)) leftMods
      where
        step (ren, used) modName =
          case M.lookup modName ren of
            Just _ -> Right (ren, used)
            Nothing ->
              if modName `S.member` used
                then
                  let (fresh, used') = freshModName pref modName used
                  in Right (M.insert modName fresh ren, used')
                else
                  Right (M.insert modName modName ren, S.insert modName used)

    buildModesFinal inlRen inrRen leftMt rightMt =
      let rightModes =
            M.fromList
              [ (renameModeName inrRen mode, ModeInfo { miName = renameModeName inrRen mode })
              | mode <- M.keys (mtModes rightMt)
              ]
      in foldl addLeft rightModes (M.keys (mtModes leftMt))
      where
        addLeft mp mode =
          let mode' = renameModeName inlRen mode
          in M.insertWith (\_ old -> old) mode' (ModeInfo { miName = mode' }) mp

    renamedDeclMap modeRen modRen mt =
      pure
        ( M.fromList
            [ (name', renameDecl modeRen modRen decl)
            | (name, decl) <- M.toList (mtDecls mt)
            , let name' = renameModName modRen name
            ]
        )

    renamedLiftMap modeRen modRen mt =
      pure
        ( M.fromList
            [ (name', renameModExpr modeRen modRen me)
            | (name, me) <- M.toList (mtClassifierLifts mt)
            , let name' = renameModName modRen name
            ]
        )

    addGlueEqn pref inlModeRen' inlModRen' inrModeRen' inrModRen' (decls, eqns) srcMod = do
      leftExpr0 <- lookupModImage "left" leftMor srcMod
      rightExpr0 <- lookupModImage "right" rightMor srcMod
      let leftExpr = renameModExpr inlModeRen' inlModRen' leftExpr0
      let rightExpr = renameModExpr inrModeRen' inrModRen' rightExpr0
      if meSrc leftExpr /= meSrc rightExpr || meTgt leftExpr /= meTgt rightExpr
        then Left "mode pushout: interface modality images have mismatched endpoints"
        else
          case (mePath leftExpr, mePath rightExpr) of
            (pL, pR) | pL == pR -> Right (decls, eqns)
            ([], []) -> Right (decls, eqns)
            ([], _) ->
              Right (decls, eqns <> [ModEqn rightExpr (identityExpr leftExpr)])
            (_, []) ->
              Right (decls, eqns <> [ModEqn leftExpr (identityExpr leftExpr)])
            ([_], [_]) ->
              Left "mode pushout: single-generator modality images should be unified by renaming"
            ([_], _) ->
              Right (decls, eqns <> [ModEqn rightExpr leftExpr])
            (_, [_]) ->
              Right (decls, eqns <> [ModEqn leftExpr rightExpr])
            _ -> do
              let base = ModName (renderModName srcMod)
              let used = S.fromList (M.keys decls)
              let (fresh, _) = freshModName pref base used
              let repExpr =
                    ModExpr
                      { meSrc = meSrc leftExpr
                      , meTgt = meTgt leftExpr
                      , mePath = [fresh]
                      }
              let repDecl =
                    ModDecl
                      { mdName = fresh
                      , mdSrc = meSrc leftExpr
                      , mdTgt = meTgt leftExpr
                      }
              let decls' = M.insert fresh repDecl decls
              Right (decls', eqns <> [ModEqn leftExpr repExpr, ModEqn rightExpr repExpr])


mergeTransformsPreferRightWithWitness
  :: Text
  -> M.Map ModeName ModeName
  -> M.Map ModName ModName
  -> GenRenameMap
  -> M.Map ModeName ModeName
  -> M.Map ModName ModName
  -> GenRenameMap
  -> ModeTheory
  -> ModeTheory
  -> Either Text (M.Map ModTransformName ModTransformDecl)
mergeTransformsPreferRightWithWitness
  prefix
  inlModeRen
  inlModRen
  inlGenRen
  inrModeRen
  inrModRen
  inrGenRen
  leftMt
  rightMt = do
  let rightRenamed =
        M.fromList
          [ (name, renameWithWitness inrModeRen inrModRen inrGenRen decl)
          | (name, decl) <- M.toList (mtTransforms rightMt)
          ]
  foldM addLeft rightRenamed (M.toList (mtTransforms leftMt))
  where
    renameWithWitness modeRen modRen genRen decl =
      let decl0 = renameTransform modeRen modRen decl
          witnessMode0 = meTgt (mtdFrom decl)
          witness0 = mtdWitness decl
          witness' = M.findWithDefault witness0 (witnessMode0, witness0) genRen
      in decl0 { mtdWitness = witness' }

    addLeft acc (name, decl) =
      let decl0 = renameWithWitness inlModeRen inlModRen inlGenRen decl
          used = S.fromList (M.keys acc)
          (name', _) =
            if name `S.member` used
              then freshTransformName prefix name used
              else (name, used)
          decl' = decl0 { mtdName = name' }
      in case M.lookup name' acc of
          Nothing -> Right (M.insert name' decl' acc)
          Just existing
            | existing == decl' -> Right acc
            | otherwise -> Left "mode pushout: conflicting modality transforms"

lookupModeImage :: Text -> Morphism -> ModeName -> Either Text ModeName
lookupModeImage side mor srcMode =
  case M.lookup srcMode (morModeMap mor) of
    Nothing -> Left ("mode pushout: missing " <> side <> " mode mapping")
    Just out -> Right out

lookupModImage :: Text -> Morphism -> ModName -> Either Text ModExpr
lookupModImage side mor srcMod =
  case M.lookup srcMod (morModMap mor) of
    Nothing -> Left ("mode pushout: missing " <> side <> " modality mapping")
    Just out -> Right out

renameModeName :: M.Map ModeName ModeName -> ModeName -> ModeName
renameModeName ren mode = M.findWithDefault mode mode ren

renameModName :: M.Map ModName ModName -> ModName -> ModName
renameModName ren modName = M.findWithDefault modName modName ren

renameModExpr :: M.Map ModeName ModeName -> M.Map ModName ModName -> ModExpr -> ModExpr
renameModExpr modeRen modRen me =
  me
    { meSrc = renameModeName modeRen (meSrc me)
    , meTgt = renameModeName modeRen (meTgt me)
    , mePath = map (renameModName modRen) (mePath me)
    }

renameModEqn :: M.Map ModeName ModeName -> M.Map ModName ModName -> ModEqn -> ModEqn
renameModEqn modeRen modRen (ModEqn lhs rhs) =
  ModEqn
    { meLHS = renameModExpr modeRen modRen lhs
    , meRHS = renameModExpr modeRen modRen rhs
    }

renameDecl :: M.Map ModeName ModeName -> M.Map ModName ModName -> ModDecl -> ModDecl
renameDecl modeRen modRen decl =
  decl
    { mdName = renameModName modRen (mdName decl)
    , mdSrc = renameModeName modeRen (mdSrc decl)
    , mdTgt = renameModeName modeRen (mdTgt decl)
    }

renameTransform :: M.Map ModeName ModeName -> M.Map ModName ModName -> ModTransformDecl -> ModTransformDecl
renameTransform modeRen modRen decl =
  decl
    { mtdFrom = renameModExpr modeRen modRen (mtdFrom decl)
    , mtdTo = renameModExpr modeRen modRen (mtdTo decl)
    }

identityExpr :: ModExpr -> ModExpr
identityExpr me =
  ModExpr
    { meSrc = meSrc me
    , meTgt = meSrc me
    , mePath = []
    }

renderModeName :: ModeName -> Text
renderModeName (ModeName t) = t

renderModName :: ModName -> Text
renderModName (ModName t) = t

mergeNamedMapsByEq :: (Ord k, Eq v) => Text -> M.Map k v -> M.Map k v -> Either Text (M.Map k v)
mergeNamedMapsByEq errMsg leftMap rightMap =
  foldM step leftMap (M.toList rightMap)
  where
    step acc (name, value) =
      case M.lookup name acc of
        Nothing -> Right (M.insert name value acc)
        Just existing
          | existing == value -> Right acc
          | otherwise -> Left errMsg

mergeClassifiedByPreferRight
  :: M.Map ModeName ClassificationDecl
  -> M.Map ModeName ClassificationDecl
  -> M.Map ModeName ClassificationDecl
mergeClassifiedByPreferRight rightMap leftMap = M.union rightMap leftMap

renamedClassifiedByMap
  :: M.Map ModeName ModeName
  -> M.Map ModName ModName
  -> TypeRenameMap
  -> TypePermMap
  -> GenRenameMap
  -> ModeTheory
  -> Either Text (M.Map ModeName ClassificationDecl)
renamedClassifiedByMap modeRen modRen tyRen permRen genRen mt =
  foldM addOne M.empty (M.toList (mtClassifiedBy mt))
  where
    addOne acc (mode, decl) = do
      universe' <- renameObjExpr modeRen modRen tyRen permRen (cdUniverse decl)
      comp' <- traverse (renameComp mode) (cdComp decl)
      let mode' = renameModeName modeRen mode
      let decl' =
            decl
              { cdClassifier = renameModeName modeRen (cdClassifier decl)
              , cdUniverse = universe'
              , cdComp = comp'
              }
      case M.lookup mode' acc of
        Nothing -> Right (M.insert mode' decl' acc)
        Just existing
          | existing == decl' -> Right acc
          | otherwise -> Right acc

    renameComp mode comp =
      let renameGen g = M.findWithDefault g (mode, g) genRen
       in Right
            comp
              { compCtxExt = renameGen (compCtxExt comp)
              , compVar = renameGen (compVar comp)
              , compReindex = renameGen (compReindex comp)
              }

computePolyCoproduct :: Text -> Doctrine -> Doctrine -> Either Text PolyPushoutResult
computePolyCoproduct name a b = do
  let empty = Doctrine
        { dName = "Empty"
        , dModes = emptyModeTheory
        , dAcyclicModes = S.empty
        , dAttrSorts = M.empty
        , dGens = M.empty
        , dCells2 = []
        , dActions = M.empty
        , dObligations = []
        }
  let morA = Morphism
        { morName = "coproduct.inl0"
        , morSrc = empty
        , morTgt = a
        , morIsCoercion = True
        , morModeMap = M.empty
        , morModMap = M.empty
        , morAttrSortMap = M.empty
        , morTypeMap = M.empty
        , morGenMap = M.empty
        , morCheck = CheckAll
        , morPolicy = UseAllOriented
        }
  let morB = Morphism
        { morName = "coproduct.inr0"
        , morSrc = empty
        , morTgt = b
        , morIsCoercion = True
        , morModeMap = M.empty
        , morModMap = M.empty
        , morAttrSortMap = M.empty
        , morTypeMap = M.empty
        , morGenMap = M.empty
        , morCheck = CheckAll
        , morPolicy = UseAllOriented
        }
  computePolyPushout name morA morB

requireTypeRenameMap :: Morphism -> Either Text (TypeRenameMap, TypePermMap)
requireTypeRenameMap mor = do
  let src = morSrc mor
  let tgt = morTgt mor
  srcCtorTables <- deriveCtorTables src
  tgtCtorTables <- deriveCtorTables tgt
  types <- allCtorsInTables src srcCtorTables
  entries <- mapM (typeImage mor tgtCtorTables) types
  let typeMap = M.fromList [ (srcRef, tgtRef) | (srcRef, tgtRef, _) <- entries ]
  permMap <- foldM insertPerm M.empty entries
  pure (typeMap, permMap)
  where
    typeImage m ctorTablesTgt (srcRef, sig) = do
      (tgtRef, mPerm) <- case M.lookup srcRef (morTypeMap m) of
        Nothing -> do
          tgtMode <- applyMorphismMode m (orMode srcRef)
          Right (srcRef { orMode = tgtMode }, Nothing)
        Just tmpl -> templateTarget tmpl (sig)
      ensureTypeExistsInTables (morTgt m) ctorTablesTgt tgtRef (length (sig))
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
        OCon tgtRef args
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
        (TPS_Ty _, TPType _) -> True
        (TPS_Tm _, TPTm _) -> True
        _ -> False

    argParamIndex params arg =
      case arg of
        OAObj (OVar v) ->
          findParamIndex params (\p -> case p of TPType v' -> v' == v; _ -> False)
        OATm tm ->
          case termMetaOnly tm of
            Just v ->
              findParamIndex params (\p -> case p of TPTm v' -> v' == v; _ -> False)
            Nothing -> Nothing
        _ -> Nothing

    termMetaOnly (TermDiagram diag) =
      case (IM.elems (dEdges diag), dIn diag, dOut diag) of
        ([edge], [], [outBoundary]) ->
          case (ePayload edge, eIns edge, eOuts edge) of
            (PTmMeta v, [], [outPid]) | outPid == outBoundary -> Just v
            _ -> Nothing
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
          Nothing ->
            if M.member srcSort tgtSorts
              then Right (srcSort, srcSort)
              else Left "poly pushout: target attrsort missing for implicit identity mapping"
          Just tgtSort ->
            if M.member tgtSort tgtSorts
              then Right (srcSort, tgtSort)
              else Left "poly pushout: target attrsort missing"
  pairs <- mapM mapOne srcSorts
  pure (M.fromList pairs)

invertPermutation :: Int -> [Int] -> Either Text [Int]
invertPermutation n perm
  | length perm /= n = Left "poly pushout: type permutation arity mismatch"
  | any outOfRange perm = Left "poly pushout: type permutation position out of range"
  | length (S.fromList perm) /= n = Left "poly pushout: type permutation is not a bijection"
  | otherwise =
      let mp = IM.fromList (zip perm [0..])
      in Right [ mp IM.! i | i <- [0..n-1] ]
  where
    outOfRange i = i < 0 || i >= n

requireGenRenameMap :: Morphism -> Either Text (M.Map (ModeName, GenName) GenName)
requireGenRenameMap mor = do
  let src = morSrc mor
  srcCtorTables <- deriveCtorTables src
  let gens = allGensInTables src srcCtorTables
  fmap M.fromList (mapM (genImage mor) gens)
  where
    genImage m (mode, gen) = do
      img <- case M.lookup (mode, gdName gen) (morGenMap m) of
        Nothing
          | isComprehensionSupportGenInDoc (morSrc m) mode (gdName gen) -> do
              tgtMode <- applyMorphismMode m mode
              ensureGenExists (morTgt m) tgtMode (gdName gen)
              Right (gdName gen)
        Nothing -> Left "poly pushout requires explicit generator mappings"
        Just d -> do
          imgName <- singleGenName m gen d
          tgtMode <- applyMorphismMode m mode
          ensureGenExists (morTgt m) tgtMode imgName
          Right imgName
      pure ((mode, gdName gen), img)

isComprehensionSupportGenInDoc :: Doctrine -> ModeName -> GenName -> Bool
isComprehensionSupportGenInDoc doc mode genName =
  case M.lookup mode (mtClassifiedBy (dModes doc)) >>= cdComp of
    Just comp ->
      genName == compCtxExt comp
        || genName == compVar comp
        || genName == compReindex comp
    Nothing -> False

singleGenName :: Morphism -> GenDecl -> GenImage -> Either Text GenName
singleGenName mor srcGen image0 = do
  binderSlotsTgt <- mapM (applyMorphismBinderSig mor) binderSlotsSrc
  let expectedBinderSigs = M.fromList (zip holes binderSlotsTgt)
  if giBinderSigs image0 == expectedBinderSigs
    then Right ()
    else Left "poly pushout requires generator mappings to preserve binder-hole signatures"
  canon <- canonDiagramRaw (giDiagram image0)
  case IM.elems (dEdges canon) of
    [edge] -> do
      let boundary = dIn canon <> dOut canon
      let edgePorts = eIns edge <> eOuts edge
      let allPorts = diagramPortIds canon
      expectedAttrs <- expectedAttrMap mor srcGen
      case ePayload edge of
        PGen g attrs bargs ->
          if boundary == edgePorts && length allPorts == length boundary && bargs == expectedBargs && attrs == expectedAttrs
            then Right g
            else Left "poly pushout requires generator mappings to be a single generator"
        _ -> Left "poly pushout requires generator mappings to be a single generator"
    _ -> Left "poly pushout requires generator mappings to be a single generator"
  where
    binderSlotsSrc = [ bs | InBinder bs <- gdDom srcGen ]
    holes = [ BinderMetaVar ("b" <> T.pack (show i)) | i <- [0 .. length binderSlotsSrc - 1] ]
    expectedBargs = map BAMeta holes
    expectedAttrMap m gen = fmap M.fromList (mapM toField (gdAttrs gen))
      where
        toField (fieldName, srcSort) = do
          tgtSort <-
            case M.lookup srcSort (morAttrSortMap m) of
              Nothing -> Left "poly pushout: missing attrsort mapping in generator image"
              Just s -> Right s
          Right (fieldName, ATVar (AttrVar fieldName tgtSort))

ensureTypeExistsInTables :: Doctrine -> CtorTables -> ObjRef -> Int -> Either Text ()
ensureTypeExistsInTables doc ctorTables ref arity =
  case lookupCtorSigByRefInTables doc ctorTables ref of
    Left _ -> Left "poly pushout: target type missing"
    Right sig
      | length (sig) == arity -> Right ()
      | otherwise -> Left "poly pushout: target type arity mismatch"

ensureGenExists :: Doctrine -> ModeName -> GenName -> Either Text ()
ensureGenExists doc mode name =
  case M.lookup mode (dGens doc) >>= M.lookup name of
    Nothing ->
      let GenName g = name
      in Left
          ( "poly pushout: target generator missing: "
              <> renderModeName mode
              <> "."
              <> g
              <> " in "
              <> dName doc
          )
    Just _ -> Right ()

groupByImage :: (Ord src, Ord img) => M.Map src img -> M.Map img [src]
groupByImage mp =
  M.fromListWith (<>) [ (img, [src]) | (src, img) <- M.toList mp ]

classRepresentatives :: (Ord a) => [a] -> [M.Map b [a]] -> Either Text (M.Map a a)
classRepresentatives items groupedMaps = do
  let nodes = S.fromList items
  let adj0 = M.fromSet (const S.empty) nodes
  let groups = concatMap M.elems groupedMaps
  let adj = foldl connectGroup adj0 groups
  pure (buildRepMap nodes adj)
  where
    connectGroup adj group =
      case group of
        [] -> adj
        (x:rest) ->
          foldl (\acc y -> connect x y acc) adj rest

    connect x y adj =
      let adj1 = M.insertWith S.union x (S.singleton y) adj
      in M.insertWith S.union y (S.singleton x) adj1

    buildRepMap nodes adj = go nodes M.empty
      where
        go remaining reps =
          case S.lookupMin remaining of
            Nothing -> reps
            Just start ->
              let component = dfs S.empty [start]
                  rep = S.findMin component
                  reps' = foldl (\mp node -> M.insert node rep mp) reps (S.toList component)
                  remaining' = S.difference remaining component
              in go remaining' reps'

        dfs seen stack =
          case stack of
            [] -> seen
            (x:xs)
              | x `S.member` seen -> dfs seen xs
              | otherwise ->
                  let neighbors = S.toList (M.findWithDefault S.empty x adj)
                  in dfs (S.insert x seen) (neighbors <> xs)

imageToRepresentative
  :: (Ord src, Ord img, Ord rep)
  => Text
  -> M.Map src img
  -> M.Map src rep
  -> Either Text (M.Map img rep)
imageToRepresentative label srcToImg reps =
  foldM add M.empty (M.toList srcToImg)
  where
    add acc (srcItem, imgItem) = do
      rep <-
        case M.lookup srcItem reps of
          Nothing ->
            Left ("poly pushout: missing class representative for " <> label)
          Just r -> Right r
      case M.lookup imgItem acc of
        Nothing -> Right (M.insert imgItem rep acc)
        Just existing
          | existing == rep -> Right acc
          | otherwise ->
              Left ("poly pushout: incompatible merged " <> label <> " images")

canonicalTypeNamesFromRight
  :: M.Map ObjRef ObjRef
  -> M.Map ObjRef ObjRef
  -> Either Text (M.Map ObjRef ObjName)
canonicalTypeNamesFromRight reps rightMap =
  foldM add M.empty (S.toList (S.fromList (M.elems reps)))
  where
    add acc repSrc = do
      imgRight <-
        case M.lookup repSrc rightMap of
          Nothing -> Left "poly pushout: missing right image for type representative"
          Just out -> Right out
      let canon = orName imgRight
      case M.lookup repSrc acc of
        Nothing -> Right (M.insert repSrc canon acc)
        Just existing
          | existing == canon -> Right acc
          | otherwise -> Left "poly pushout: inconsistent canonical type representative"

imageTypesToCanonicalNames
  :: Text
  -> M.Map ObjRef ObjRef
  -> M.Map ObjRef ObjRef
  -> M.Map ObjRef ObjName
  -> Either Text TypeRenameMap
imageTypesToCanonicalNames label srcToImg reps canonNames =
  foldM add M.empty (M.toList srcToImg)
  where
    add acc (srcRef, imgRef) = do
      repSrc <-
        case M.lookup srcRef reps of
          Nothing -> Left ("poly pushout: missing class representative for " <> label)
          Just out -> Right out
      canonName <-
        case M.lookup repSrc canonNames of
          Nothing -> Left ("poly pushout: missing canonical " <> label <> " name")
          Just out -> Right out
      let imgRef' = imgRef { orName = canonName }
      case M.lookup imgRef acc of
        Nothing -> Right (M.insert imgRef imgRef' acc)
        Just existing
          | existing == imgRef' -> Right acc
          | otherwise -> Left ("poly pushout: incompatible merged " <> label <> " images")

interfaceCellKeys :: Morphism -> Either Text (S.Set (ModeName, Text))
interfaceCellKeys mor =
  fmap S.fromList (mapM toKey (dCells2 (morSrc mor)))
  where
    toKey cell = do
      tgtMode <- applyMorphismMode mor (dMode (c2LHS cell))
      Right (tgtMode, c2Name cell)

generatorImageKeys
  :: Morphism
  -> M.Map (ModeName, GenName) GenName
  -> Either Text (M.Map (ModeName, GenName) (ModeName, GenName))
generatorImageKeys mor genMap =
  fmap M.fromList (mapM toKey (M.toList genMap))
  where
    toKey ((srcMode, srcName), imgName) = do
      tgtMode <- applyMorphismMode mor srcMode
      Right ((srcMode, srcName), (tgtMode, imgName))

ensureAttrSortClassCompat :: Doctrine -> M.Map AttrSort AttrSort -> Either Text ()
ensureAttrSortClassCompat src reps =
  mapM_ checkGroup (M.elems groups)
  where
    groups = M.fromListWith (<>) [ (rep, [srcSort]) | (srcSort, rep) <- M.toList reps ]
    decls = dAttrSorts src
    checkGroup members =
      case members of
        [] -> Right ()
        (firstSort:rest) -> do
          firstDecl <- lookupDecl firstSort
          mapM_ (checkOne firstDecl) rest
    lookupDecl sortName =
      case M.lookup sortName decls of
        Nothing -> Left "poly pushout: missing source attrsort declaration"
        Just decl -> Right decl
    checkOne firstDecl sortName = do
      decl <- lookupDecl sortName
      if decl == firstDecl
        then Right ()
        else Left "poly pushout: incompatible merged attrsort signatures"

ensureTypeClassCompat :: [(ObjRef, [TypeParamSig])] -> M.Map ObjRef ObjRef -> Either Text ()
ensureTypeClassCompat srcCtors reps =
  mapM_ checkGroup (M.elems groups)
  where
    groups = M.fromListWith (<>) [ (rep, [srcRef]) | (srcRef, rep) <- M.toList reps ]
    sigByRef = M.fromList srcCtors
    checkGroup members =
      case members of
        [] -> Right ()
        (firstRef:rest) -> do
          firstSig <- lookupSig firstRef
          mapM_ (checkOne firstSig) rest
    lookupSig ref =
      case M.lookup ref sigByRef of
        Nothing -> Left "poly pushout: missing source type signature"
        Just sig -> Right sig
    checkOne firstSig ref = do
      sig <- lookupSig ref
      if sig == firstSig
        then Right ()
        else Left "poly pushout: incompatible merged type signatures"

ensureGenClassCompat :: [(ModeName, GenDecl)] -> M.Map (ModeName, GenName) (ModeName, GenName) -> Either Text ()
ensureGenClassCompat srcGens reps =
  mapM_ checkGroup (M.elems groups)
  where
    groups = M.fromListWith (<>) [ (rep, [srcKey]) | (srcKey, rep) <- M.toList reps ]
    genByKey = M.fromList [ ((mode, gdName genDecl), genDecl) | (mode, genDecl) <- srcGens ]
    checkGroup members =
      case members of
        [] -> Right ()
        (firstKey:rest) -> do
          firstGen <- lookupGenDecl firstKey
          mapM_ (checkOne firstGen) rest
    lookupGenDecl key =
      case M.lookup key genByKey of
        Nothing -> Left "poly pushout: missing source generator declaration"
        Just genDecl -> Right genDecl
    checkOne firstGen key = do
      genDecl <- lookupGenDecl key
      if genDeclAlphaEqIgnoringName firstGen genDecl
        then Right ()
        else Left "poly pushout: incompatible merged generator signatures"

disjointTypeRenames :: M.Map ModeName ModeName -> Text -> TypeRenameMap -> CtorTables -> Doctrine -> Either Text TypeRenameMap
disjointTypeRenames modeRen prefix interfaceRen tgtCtorTables tgt = do
  refs <- map fst <$> allCtorsInTables tgt tgtCtorTables
  pure (fst (foldl step (M.empty, used0) refs))
  where
    interfaceNamesByFinalMode =
      namesByMode
        [ (renameModeName modeRen (orMode ref), orName ref)
        | ref <- M.elems interfaceRen
        ]
    used0 = interfaceNamesByFinalMode
    step (renAcc, usedByFinalMode) srcRef =
      let modeSrc = orMode srcRef
          modeFinal = renameModeName modeRen modeSrc
          nameSrc = orName srcRef
          used = M.findWithDefault S.empty modeFinal usedByFinalMode
      in case M.lookup srcRef interfaceRen of
          Just tgtRef ->
            let usedByFinalMode' = M.insert modeFinal (S.insert (orName tgtRef) used) usedByFinalMode
            in (renAcc, usedByFinalMode')
          Nothing ->
            if isUniverseCtorRef tgt srcRef
              then
                let usedByFinalMode' = M.insert modeFinal (S.insert nameSrc used) usedByFinalMode
                in (renAcc, usedByFinalMode')
              else
                let (fresh, used') = freshTypeName prefix nameSrc used
                    renAcc' = M.insert srcRef (ObjRef modeSrc fresh) renAcc
                    usedByFinalMode' = M.insert modeFinal used' usedByFinalMode
                in (renAcc', usedByFinalMode')

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

disjointGenRenames :: M.Map ModeName ModeName -> Text -> GenRenameMap -> Doctrine -> GenRenameMap
disjointGenRenames modeRen prefix interfaceRen tgt =
  fst (foldl step (M.empty, used0) keys)
  where
    interfaceNamesByFinalMode =
      namesByMode
        [ (renameModeName modeRen mode, name)
        | ((mode, _), name) <- M.toList interfaceRen
        ]
    used0 = interfaceNamesByFinalMode
    keys =
      [ (mode, gdName gen)
      | (mode, table) <- M.toList (dGens tgt)
      , gen <- M.elems table
      ]
    step (renAcc, usedByFinalMode) srcKey@(modeSrc, nameSrc) =
      let modeFinal = renameModeName modeRen modeSrc
          used = M.findWithDefault S.empty modeFinal usedByFinalMode
      in case M.lookup srcKey interfaceRen of
          Just tgtName ->
            let usedByFinalMode' = M.insert modeFinal (S.insert tgtName used) usedByFinalMode
            in (renAcc, usedByFinalMode')
          Nothing ->
            let (fresh, used') = freshGenName prefix nameSrc used
                renAcc' = M.insert srcKey fresh renAcc
                usedByFinalMode' = M.insert modeFinal used' usedByFinalMode
            in (renAcc', usedByFinalMode')

disjointCellRenames :: M.Map ModeName ModeName -> Text -> S.Set (ModeName, Text) -> Doctrine -> CellRenameMap
disjointCellRenames modeRen prefix interfaceKeys tgt =
  fst (foldl step (M.empty, used0) (dCells2 tgt))
  where
    interfaceNamesByFinalMode =
      namesByMode
        [ (renameModeName modeRen mode, name)
        | (mode, name) <- S.toList interfaceKeys
        ]
    used0 = interfaceNamesByFinalMode
    step (renAcc, usedByFinalMode) cell =
      let mode0 = dMode (c2LHS cell)
          modeFinal = renameModeName modeRen mode0
          name = c2Name cell
          used = M.findWithDefault S.empty modeFinal usedByFinalMode
          isInterface = S.member (mode0, name) interfaceKeys
      in if isInterface
        then (renAcc, M.insert modeFinal (S.insert name used) usedByFinalMode)
        else
          let (fresh, used') = freshCellName prefix name used
              renAcc' = M.insert (mode0, name) fresh renAcc
              usedByFinalMode' = M.insert modeFinal used' usedByFinalMode
          in (renAcc', usedByFinalMode')

disjointObligationRenames :: Text -> Doctrine -> Doctrine -> OblRenameMap
disjointObligationRenames prefix src tgt =
  snd (foldl step (srcNames, M.empty) (dObligations tgt))
  where
    srcNames = S.fromList (map obName (dObligations src))
    step (used, mp) obl =
      let name = obName obl
      in if name `S.member` used
        then (used, mp)
        else
          let (name', used') = freshCellName prefix name used
          in (used', M.insert name name' mp)

disjointTransformRenames :: Text -> Doctrine -> Doctrine -> TransformRenameMap
disjointTransformRenames prefix src tgt =
  snd (foldl step (srcNames, M.empty) (M.keys (mtTransforms (dModes tgt))))
  where
    srcNames = S.fromList (M.keys (mtTransforms (dModes src)))
    step (used, mp) name =
      if name `S.member` used
        then (used, mp)
        else
          let (name', used') = freshTransformName prefix name used
          in (used', M.insert name name' mp)

mkInterfaceAttrSortRenameMap :: AttrSortRenameMap -> AttrSortRenameMap -> Either Text AttrSortRenameMap
mkInterfaceAttrSortRenameMap leftMap rightMap =
  foldM add M.empty (M.toList leftMap)
  where
    add acc (srcSort, imgLeft) = do
      imgRight <-
        case M.lookup srcSort rightMap of
          Nothing -> Left "apply pushout: missing interface attrsort mapping on right morphism"
          Just out -> Right out
      case M.lookup imgLeft acc of
        Nothing -> Right (M.insert imgLeft imgRight acc)
        Just existing
          | existing == imgRight -> Right acc
          | otherwise -> Left "apply pushout: inconsistent attrsort interface images"

mkInterfaceTypeRenameMap
  :: Doctrine
  -> CtorTables
  -> TypeRenameMap
  -> TypePermMap
  -> TypeRenameMap
  -> TypePermMap
  -> Either Text (TypeRenameMap, TypePermMap)
mkInterfaceTypeRenameMap src srcCtorTables leftMap leftPerm rightMap rightPerm = do
  srcCtors <- allCtorsInTables src srcCtorTables
  foldM add (M.empty, M.empty) srcCtors
  where
    add (renAcc, permAcc) (srcRef, sig) = do
      imgLeft <-
        case M.lookup srcRef leftMap of
          Nothing -> Left "apply pushout: missing interface type mapping on left morphism"
          Just out -> Right out
      imgRight <-
        case M.lookup srcRef rightMap of
          Nothing -> Left "apply pushout: missing interface type mapping on right morphism"
          Just out -> Right out
      renAcc' <-
        case M.lookup imgLeft renAcc of
          Nothing -> Right (M.insert imgLeft imgRight renAcc)
          Just existing
            | existing == imgRight -> Right renAcc
            | otherwise -> Left "apply pushout: inconsistent type interface images"
      let arity = length (sig)
      invLeft <- normalizeInvPerm arity (M.lookup imgLeft leftPerm)
      invRight <- normalizeInvPerm arity (M.lookup imgRight rightPerm)
      rightPermFwd <- invertPermutation arity invRight
      let perm = [ invLeft !! i | i <- rightPermFwd ]
      let ident = [0 .. arity - 1]
      permAcc' <-
        if perm == ident
          then Right permAcc
          else
            case M.lookup imgLeft permAcc of
              Nothing -> Right (M.insert imgLeft perm permAcc)
              Just existing
                | existing == perm -> Right permAcc
                | otherwise -> Left "apply pushout: inconsistent type interface permutations"
      pure (renAcc', permAcc')

    normalizeInvPerm n mPerm =
      case mPerm of
        Nothing -> Right [0 .. n - 1]
        Just perm -> do
          if length perm == n
            then Right perm
            else Left "apply pushout: interface permutation arity mismatch"

mkInterfaceGenRenameMap
  :: M.Map (ModeName, GenName) GenName
  -> M.Map (ModeName, GenName) GenName
  -> Either Text (M.Map (ModeName, GenName) GenName)
mkInterfaceGenRenameMap leftMap rightMap =
  foldM add M.empty (M.toList leftMap)
  where
    add acc (srcKey, imgLeft) = do
      imgRight <-
        case M.lookup srcKey rightMap of
          Nothing -> Left "apply pushout: missing interface generator mapping on right morphism"
          Just out -> Right out
      let outKey = (fst srcKey, imgLeft)
      case M.lookup outKey acc of
        Nothing -> Right (M.insert outKey imgRight acc)
        Just existing
          | existing == imgRight -> Right acc
          | otherwise -> Left "apply pushout: inconsistent generator interface images"

collisionTypeRenames
  :: M.Map ModeName ModeName
  -> Text
  -> TypeRenameMap
  -> Doctrine
  -> CtorTables
  -> Doctrine
  -> CtorTables
  -> Either Text TypeRenameMap
collisionTypeRenames modeRen prefix interfaceRen target targetCtorTables body bodyCtorTables = do
  targetCtors <- allCtorsInTables target targetCtorTables
  bodyCtors <- allCtorsInTables body bodyCtorTables
  let targetNamesByFinalMode =
        namesByMode
          [ (orMode ref, orName ref)
          | (ref, _) <- targetCtors
          ]
      interfaceTargetsByFinalMode =
        namesByMode
          [ (orMode ref, orName ref)
          | ref <- M.elems interfaceRen
          ]
      used0 = M.unionWith S.union targetNamesByFinalMode interfaceTargetsByFinalMode
      bodyRefs = map fst bodyCtors
  pure (fst (foldl step (M.empty, used0) bodyRefs))
  where
    step (renAcc, usedByFinalMode) srcRef =
      let modeSrc = orMode srcRef
          nameSrc = orName srcRef
          modeFinal = renameModeName modeRen modeSrc
          used = M.findWithDefault S.empty modeFinal usedByFinalMode
      in case M.lookup srcRef interfaceRen of
          Just tgtRef ->
            let used' = M.insert modeFinal (S.insert (orName tgtRef) used) usedByFinalMode
            in (renAcc, used')
          Nothing ->
            if nameSrc `S.member` used && not (isUniverseCtorRef body srcRef)
              then
                let (fresh, used') = freshTypeName prefix nameSrc used
                    renAcc' = M.insert srcRef (ObjRef modeSrc fresh) renAcc
                    usedByFinalMode' = M.insert modeFinal used' usedByFinalMode
                in (renAcc', usedByFinalMode')
              else
                let usedByFinalMode' = M.insert modeFinal (S.insert nameSrc used) usedByFinalMode
                in (renAcc, usedByFinalMode')

isUniverseCtorRef :: Doctrine -> ObjRef -> Bool
isUniverseCtorRef doc ref =
  any matches (M.elems (mtClassifiedBy (dModes doc)))
  where
    matches decl =
      case cdUniverse decl of
        OCon uRef [] -> uRef == ref
        _ -> False

collisionAttrSortRenames :: Text -> AttrSortRenameMap -> Doctrine -> Doctrine -> AttrSortRenameMap
collisionAttrSortRenames prefix interfaceRen target body =
  fst (foldl step (M.empty, used0) (M.keys (dAttrSorts body)))
  where
    used0 = S.union (S.fromList (M.keys (dAttrSorts target))) (S.fromList (M.elems interfaceRen))
    step (renAcc, used) name =
      if M.member name interfaceRen
        then (renAcc, used)
        else
          if name `S.member` used
            then
              let (fresh, used') = freshAttrSortName prefix name used
              in (M.insert name fresh renAcc, used')
            else (renAcc, S.insert name used)

collisionGenRenames
  :: M.Map ModeName ModeName
  -> Text
  -> M.Map (ModeName, GenName) GenName
  -> Doctrine
  -> Doctrine
  -> M.Map (ModeName, GenName) GenName
collisionGenRenames modeRen prefix interfaceRen target body =
  fst (foldl step (M.empty, used0) bodyKeys)
  where
    targetNamesByFinalMode =
      namesByMode
        [ (mode, gdName gen)
        | (mode, table) <- M.toList (dGens target)
        , gen <- M.elems table
        ]
    interfaceTargetsByFinalMode =
      namesByMode
        [ (renameModeName modeRen mode, name)
        | ((mode, _), name) <- M.toList interfaceRen
        ]
    used0 = M.unionWith S.union targetNamesByFinalMode interfaceTargetsByFinalMode
    bodyKeys =
      [ (mode, gdName gen)
      | (mode, table) <- M.toList (dGens body)
      , gen <- M.elems table
      ]
    step (renAcc, usedByFinalMode) srcKey@(modeSrc, nameSrc) =
      let modeFinal = renameModeName modeRen modeSrc
          used = M.findWithDefault S.empty modeFinal usedByFinalMode
      in case M.lookup srcKey interfaceRen of
          Just tgtName ->
            let usedByFinalMode' = M.insert modeFinal (S.insert tgtName used) usedByFinalMode
            in (renAcc, usedByFinalMode')
          Nothing ->
            if nameSrc `S.member` used
              then
                let (fresh, used') = freshGenName prefix nameSrc used
                    renAcc' = M.insert srcKey fresh renAcc
                    usedByFinalMode' = M.insert modeFinal used' usedByFinalMode
                in (renAcc', usedByFinalMode')
              else
                let usedByFinalMode' = M.insert modeFinal (S.insert nameSrc used) usedByFinalMode
                in (renAcc, usedByFinalMode')

collisionCellRenames :: M.Map ModeName ModeName -> Text -> Doctrine -> Doctrine -> Doctrine -> M.Map (ModeName, Text) Text
collisionCellRenames modeRen prefix src target body =
  fst (foldl step (M.empty, used0) (dCells2 body))
  where
    srcNames =
      namesByMode
        [ (renameModeName modeRen (dMode (c2LHS cell)), c2Name cell)
        | cell <- dCells2 src
        ]
    used0 =
      namesByMode
        [ (dMode (c2LHS cell), c2Name cell)
        | cell <- dCells2 target
        ]
    step (renAcc, usedByMode) cell =
      let mode0 = dMode (c2LHS cell)
          modeFinal = renameModeName modeRen mode0
          name = c2Name cell
          used = M.findWithDefault S.empty modeFinal usedByMode
          isInterface = name `S.member` M.findWithDefault S.empty modeFinal srcNames
      in if isInterface
        then (renAcc, M.insert modeFinal (S.insert name used) usedByMode)
        else
          if name `S.member` used
            then
              let (fresh, used') = freshCellName prefix name used
                  usedByMode' = M.insert modeFinal used' usedByMode
              in (M.insert (mode0, name) fresh renAcc, usedByMode')
            else
              let usedByMode' = M.insert modeFinal (S.insert name used) usedByMode
              in (renAcc, usedByMode')

collisionObligationRenames :: Text -> Doctrine -> Doctrine -> Doctrine -> OblRenameMap
collisionObligationRenames prefix src target body =
  fst (foldl step (M.empty, used0) (dObligations body))
  where
    interfaceNames = S.fromList (map obName (dObligations src))
    used0 = S.fromList (map obName (dObligations target))
    step (renAcc, used) obl =
      let name = obName obl
          isInterface = name `S.member` interfaceNames
      in if isInterface
        then (renAcc, S.insert name used)
        else
          if name `S.member` used
            then
              let (fresh, used') = freshCellName prefix name used
              in (M.insert name fresh renAcc, used')
            else (renAcc, S.insert name used)

collisionTransformRenames :: Text -> Doctrine -> Doctrine -> Doctrine -> TransformRenameMap
collisionTransformRenames prefix src target body =
  fst (foldl step (M.empty, used0) (M.keys (mtTransforms (dModes body))))
  where
    interfaceNames = S.fromList (M.keys (mtTransforms (dModes src)))
    used0 = S.fromList (M.keys (mtTransforms (dModes target)))
    step (renAcc, used) name =
      let isInterface = name `S.member` interfaceNames
      in if isInterface
        then (renAcc, S.insert name used)
        else
          if name `S.member` used
            then
              let (fresh, used') = freshTransformName prefix name used
              in (M.insert name fresh renAcc, used')
            else (renAcc, S.insert name used)

namesByMode :: (Ord a) => [(ModeName, a)] -> M.Map ModeName (S.Set a)
namesByMode pairs =
  foldl add M.empty pairs
  where
    add mp (mode, name) =
      let set = M.findWithDefault S.empty mode mp
      in M.insert mode (S.insert name set) mp

sanitizePrefix :: Text -> Text
sanitizePrefix = T.map (\c -> if c == '.' then '_' else c)

freshTypeName :: Text -> ObjName -> S.Set ObjName -> (ObjName, S.Set ObjName)
freshTypeName prefix (ObjName base) used =
  let baseName = prefix <> "_" <> base
      candidate = ObjName baseName
  in freshen candidate (\n -> ObjName (baseName <> "_" <> T.pack (show n))) used

freshModeName :: Text -> ModeName -> S.Set ModeName -> (ModeName, S.Set ModeName)
freshModeName prefix (ModeName base) used =
  let baseName = prefix <> "_" <> base
      candidate = ModeName baseName
  in freshen candidate (\n -> ModeName (baseName <> "_" <> T.pack (show n))) used

freshModName :: Text -> ModName -> S.Set ModName -> (ModName, S.Set ModName)
freshModName prefix (ModName base) used =
  let baseName = prefix <> "_" <> base
      candidate = ModName baseName
  in freshen candidate (\n -> ModName (baseName <> "_" <> T.pack (show n))) used

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

freshTransformName :: Text -> ModTransformName -> S.Set ModTransformName -> (ModTransformName, S.Set ModTransformName)
freshTransformName prefix (ModTransformName base) used =
  let baseName = prefix <> "_" <> base
      candidate = ModTransformName baseName
  in freshen candidate (\n -> ModTransformName (baseName <> "_" <> T.pack (show n))) used

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
  :: M.Map ModeName ModeName
  -> M.Map ModName ModName
  -> AttrSortRenameMap
  -> TypeRenameMap
  -> TypePermMap
  -> GenRenameMap
  -> CellRenameMap
  -> OblRenameMap
  -> TransformRenameMap
  -> Doctrine
  -> Either Text Doctrine
renameDoctrine modeRen modRen attrRen tyRen permRen genRen cellRen oblRen transformRen doc = do
  modes' <- renameModeTransforms transformRen (dModes doc)
  attrSorts' <- renameAttrSorts attrRen (dAttrSorts doc)
  ctorTables <- ctorTablesByDoc
  gens' <- renameGenTables ctorTables (dGens doc)
  cells' <- mapM (renameCell modeRen modRen attrRen tyRen permRen genRen cellRen) (dCells2 doc)
  actions' <- renameActions (dActions doc)
  obligations' <- mapM renameObligation (dObligations doc)
  let acyclic' =
        S.fromList [ renameModeName modeRen m | m <- S.toList (dAcyclicModes doc) ]
  pure
    doc
      { dModes = modes'
      , dAcyclicModes = acyclic'
      , dAttrSorts = attrSorts'
      , dGens = gens'
      , dCells2 = cells'
      , dActions = actions'
      , dObligations = obligations'
      }
  where
    mt = dModes doc
    ctorTablesByDoc = deriveCtorTables doc

    renameModeTransforms transRen mt0 = do
      transforms' <- foldM addTransform M.empty (M.toList (mtTransforms mt0))
      classifiedBy' <- foldM addClassification M.empty (M.toList (mtClassifiedBy mt0))
      classifierLifts' <- foldM addClassifierLiftRenamed M.empty (M.toList (mtClassifierLifts mt0))
      let modes' =
            M.fromList
              [ (mode', info { miName = mode' })
              | (mode, info) <- M.toList (mtModes mt0)
              , let mode' = renameModeName modeRen mode
              ]
      let decls' =
            M.fromList
              [ (name', renameDecl modeRen modRen decl)
              | (name, decl) <- M.toList (mtDecls mt0)
              , let name' = renameModName modRen name
              ]
      let eqns' = map (renameModEqn modeRen modRen) (mtEqns mt0)
      Right
        mt0
          { mtModes = modes'
          , mtDecls = decls'
          , mtEqns = eqns'
          , mtTransforms = transforms'
          , mtClassifiedBy = classifiedBy'
          , mtClassifierLifts = classifierLifts'
          }
      where
        addTransform acc (name, decl) = do
          let name' = M.findWithDefault name name transRen
          let decl0 = renameTransform modeRen modRen decl
          let witnessMode0 = meTgt (mtdFrom decl)
          let witness0 = mtdWitness decl
          let witness' = M.findWithDefault witness0 (witnessMode0, witness0) genRen
          let decl' = decl0 { mtdName = name', mtdWitness = witness' }
          case M.lookup name' acc of
            Nothing -> Right (M.insert name' decl' acc)
            Just existing
              | existing == decl' -> Right acc
              | otherwise -> Left "poly pushout: modality transform name collision"

        addClassification acc (mode, decl) = do
          universe' <- renameUniverse decl
          comp' <- traverse (renameComp mode) (cdComp decl)
          let mode' = renameModeName modeRen mode
          let decl' =
                decl
                  { cdClassifier = renameModeName modeRen (cdClassifier decl)
                  , cdUniverse = universe'
                  , cdComp = comp'
                  }
          case M.lookup mode' acc of
            Nothing -> Right (M.insert mode' decl' acc)
            Just existing
              | existing == decl' -> Right acc
              | otherwise -> Right acc
          where
            renameUniverse decl0 = do
              universe1 <- renameObjExpr modeRen modRen tyRen permRen (cdUniverse decl0)
              pure (rewriteUniverseByGen decl0 universe1)

            rewriteUniverseByGen decl0 universe1 =
              case cdUniverse decl0 of
                OCon ref0 [] ->
                  case M.lookup (orMode ref0, GenName (objNameText (orName ref0))) genRen of
                    Just (GenName gName') ->
                      mkCon
                        ( ObjRef
                            { orMode = renameModeName modeRen (orMode ref0)
                            , orName = ObjName gName'
                            }
                        )
                        []
                    Nothing -> universe1
                _ -> universe1

            renameComp mode0 comp =
              let renameGen g = M.findWithDefault g (mode0, g) genRen
               in Right
                    comp
                      { compCtxExt = renameGen (compCtxExt comp)
                      , compVar = renameGen (compVar comp)
                      , compReindex = renameGen (compReindex comp)
                      }

            objNameText (ObjName t) = t

        addClassifierLiftRenamed acc (name, me) =
          let name' = renameModName modRen name
              me' = renameModExpr modeRen modRen me
           in case M.lookup name' acc of
                Nothing -> Right (M.insert name' me' acc)
                Just existing
                  | existing == me' -> Right acc
                  | otherwise -> Left "poly pushout: classifier lift collision"

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

    renameGenTables ctorTables tables =
      foldM addGen M.empty
        [ (mode, gen)
        | (mode, table) <- M.toList tables
        , gen <- M.elems table
        ]
      where
        addGen acc (mode, gen) = do
          let name'
                | isCtorLikeGen mode (gdName gen) = ctorGenName mode (gdName gen)
                | otherwise = M.findWithDefault (gdName gen) (mode, gdName gen) genRen
          let mode' = renameModeName modeRen mode
          dom' <- mapM (renameInputShape modeRen modRen tyRen permRen) (gdDom gen)
          cod' <- mapM (renameObjExpr modeRen modRen tyRen permRen) (gdCod gen)
          tyVars' <- mapM renameTyVar (gdTyVars gen)
          tmVars' <- mapM renameTmVar (gdTmVars gen)
          params0 <- rebuildParams (gdParams gen) tyVars' tmVars'
          (tyVars'', tmVars'', params') <-
            case ctorParamPerm mode (gdName gen) of
              Nothing -> Right (tyVars', tmVars', params0)
              Just perm -> permuteCtorParams perm tyVars' tmVars' params0
          let attrs' = [ (fieldName, M.findWithDefault sortName sortName attrRen) | (fieldName, sortName) <- gdAttrs gen ]
          let gen' =
                gen
                  { gdName = name'
                  , gdMode = mode'
                  , gdTyVars = tyVars''
                  , gdTmVars = tmVars''
                  , gdParams = params'
                  , gdDom = dom'
                  , gdCod = cod'
                  , gdAttrs = attrs'
                  }
          let table0 = M.findWithDefault M.empty mode' acc
          case M.lookup name' table0 of
            Nothing ->
              let table' = M.insert name' gen' table0
              in Right (M.insert mode' table' acc)
            Just existing | existing == gen' -> Right acc
            _ -> Left "poly pushout: generator name collision"

        ctorGenName mode (GenName genTxt) =
          let ref0 = ObjRef mode (ObjName genTxt)
              ref' = M.findWithDefault ref0 ref0 tyRen
              ObjName outName = orName ref'
          in GenName outName

        ctorParamPerm mode (GenName genTxt)
          | isCtorLikeGen mode (GenName genTxt) =
              M.lookup (ObjRef mode (ObjName genTxt)) permRen
          | otherwise = Nothing

        isCtorLikeGen mode (GenName genTxt) =
          isTypeDeclGenNameInTables doc ctorTables mode (ObjName genTxt)

        renameTyVar tv = do
          sort' <- renameObjExpr modeRen modRen tyRen permRen (tmvSort tv)
          Right tv { tmvSort = sort', tmvOwnerMode = fmap (renameModeName modeRen) (tmvOwnerMode tv) }
        renameTmVar tmVar = do
          sort' <- renameObjExpr modeRen modRen tyRen permRen (tmvSort tmVar)
          Right tmVar { tmvSort = sort' }

        rebuildParams [] tyVars tmVars = Right (map GP_Ty tyVars <> map GP_Tm tmVars)
        rebuildParams params tyVars tmVars = mapM rebuildOne params
          where
            rebuildOne gp =
              case gp of
                GP_Ty v ->
                  GP_Ty <$> findVar "type" v tyVars
                GP_Tm v ->
                  GP_Tm <$> findVar "term" v tmVars

        findVar label needle hay =
          case [ v | v <- hay, sameVarId v needle ] of
            [v] -> Right v
            _ -> Left ("poly pushout: failed to rebuild " <> label <> " parameter metadata")

        sameVarId a b = tmvName a == tmvName b

        permuteCtorParams perm tyVars tmVars params = do
          paramsPerm0 <- applyPerm perm params
          let tyVarsPerm = [ v | GP_Ty v <- paramsPerm0 ]
          let tmVarsPerm = [ v | GP_Tm v <- paramsPerm0 ]
          let fallbackTy = [ v | GP_Ty v <- map GP_Ty tyVars ]
          let fallbackTm = [ v | GP_Tm v <- map GP_Tm tmVars ]
          let tyOut = if null tyVarsPerm && not (null tyVars) then fallbackTy else tyVarsPerm
          let tmOut = if null tmVarsPerm && not (null tmVars) then fallbackTm else tmVarsPerm
          pure (tyOut, tmOut, paramsPerm0)

    renameActions table =
      foldM addAction M.empty (M.toList table)
      where
        addAction acc (_modName, action) = do
          let modName' = renameModName modRen (maMod action)
          genMap' <- renameActionGenMap (maGenMap action)
          let action' = action { maMod = modName', maGenMap = genMap' }
          case M.lookup modName' acc of
            Nothing -> Right (M.insert modName' action' acc)
            Just existing
              | existing == action' -> Right acc
              | otherwise -> Left "poly pushout: modality action collision"

    renameActionGenMap table =
      foldl add (Right M.empty) (M.toList table)
      where
        add acc ((mode, genName), diag) = do
          mp <- acc
          let mode' = renameModeName modeRen mode
          let genName' = M.findWithDefault genName (mode, genName) genRen
          diag' <- renameDiagram modeRen modRen attrRen tyRen permRen genRen diag
          case M.lookup (mode', genName') mp of
            Nothing -> Right (M.insert (mode', genName') diag' mp)
            Just existing
              | existing == diag' -> Right mp
              | otherwise -> Left "poly pushout: modality action generator collision"

    renameObligation obl = do
      let name' = M.findWithDefault (obName obl) (obName obl) oblRen
      let tyVarNames = S.fromList (map ovName (obTyVars obl))
      let tmVarNames = S.fromList (map tmvName (obTmVars obl))
      let mode0 = obMode obl
      let mode' = renameModeName modeRen mode0
      tyVars' <- mapM renameObTyVar (obTyVars obl)
      tmVars' <- mapM renameObTmVar (obTmVars obl)
      dom' <- mapM (renameObjExpr modeRen modRen tyRen permRen) (obDom obl)
      cod' <- mapM (renameObjExpr modeRen modRen tyRen permRen) (obCod obl)
      lhs' <- renameOblExpr tyVarNames tmVarNames mode0 (obLHSExpr obl)
      rhs' <- renameOblExpr tyVarNames tmVarNames mode0 (obRHSExpr obl)
      pure
        obl
          { obName = name'
          , obMode = mode'
          , obTyVars = tyVars'
          , obTmVars = tmVars'
          , obDom = dom'
          , obCod = cod'
          , obLHSExpr = lhs'
          , obRHSExpr = rhs'
          }
      where
        renameObTyVar tv = do
          sort' <- renameObjExpr modeRen modRen tyRen permRen (tmvSort tv)
          Right tv { tmvSort = sort', tmvOwnerMode = fmap (renameModeName modeRen) (tmvOwnerMode tv) }

        renameObTmVar tmVar = do
          sort' <- renameObjExpr modeRen modRen tyRen permRen (tmvSort tmVar)
          Right tmVar { tmvSort = sort' }

    renameRawModExpr rawMe =
      case rawMe of
        PolyAST.RMId modeNameTxt ->
          PolyAST.RMId (renderModeName (renameModeName modeRen (ModeName modeNameTxt)))
        PolyAST.RMComp toks ->
          PolyAST.RMComp
            [ renderModName (renameModName modRen (ModName tok))
            | tok <- toks
            ]

    renameOblExpr tyVarNames tmVarNames mode expr =
      case expr of
        PolyAST.ROEDiag d ->
          PolyAST.ROEDiag <$> renameRawDiagExpr tyVarNames tmVarNames mode d
        PolyAST.ROEMap me inner -> do
          (innerMode, _outerMode) <- rawModExprEndpoints mode me
          inner' <- renameOblExpr tyVarNames tmVarNames innerMode inner
          let me' = renameRawModExpr me
          pure (PolyAST.ROEMap me' inner')
        PolyAST.ROEGen ->
          Right PolyAST.ROEGen
        PolyAST.ROELiftDom d ->
          PolyAST.ROELiftDom <$> renameRawDiagExpr tyVarNames tmVarNames mode d
        PolyAST.ROELiftCod d ->
          PolyAST.ROELiftCod <$> renameRawDiagExpr tyVarNames tmVarNames mode d
        PolyAST.ROEComp a b ->
          PolyAST.ROEComp <$> renameOblExpr tyVarNames tmVarNames mode a <*> renameOblExpr tyVarNames tmVarNames mode b
        PolyAST.ROETensor a b ->
          PolyAST.ROETensor <$> renameOblExpr tyVarNames tmVarNames mode a <*> renameOblExpr tyVarNames tmVarNames mode b

    renameRawDiagExpr tyVarNames tmVarNames mode expr =
      case expr of
        PolyAST.RDId ctx ->
          PolyAST.RDId <$> mapM (renameRawTypeAsType tyVarNames tmVarNames mode) ctx
        PolyAST.RDMetaVar name ->
          Right (PolyAST.RDMetaVar name)
        PolyAST.RDGen name mTyArgs mAttrArgs mBinderArgs -> do
          let genName = GenName name
          let genName' = M.findWithDefault genName (mode, genName) genRen
          mTyArgs' <- renameRawGenArgs tyVarNames tmVarNames mode genName mTyArgs
          mBinderArgs' <- mapM (mapM (renameRawBinderArg tyVarNames tmVarNames mode)) mBinderArgs
          pure (PolyAST.RDGen (renderGenName genName') mTyArgs' mAttrArgs mBinderArgs')
        PolyAST.RDTermRef name ->
          Right (PolyAST.RDTermRef name)
        PolyAST.RDSplice name ->
          Right (PolyAST.RDSplice name)
        PolyAST.RDBox name inner ->
          PolyAST.RDBox name <$> renameRawDiagExpr tyVarNames tmVarNames mode inner
        PolyAST.RDLoop inner ->
          PolyAST.RDLoop <$> renameRawDiagExpr tyVarNames tmVarNames mode inner
        PolyAST.RDMap me inner -> do
          (innerMode, _outerMode) <- rawModExprEndpoints mode me
          inner' <- renameRawDiagExpr tyVarNames tmVarNames innerMode inner
          let me' = renameRawModExpr me
          pure (PolyAST.RDMap me' inner')
        PolyAST.RDComp a b ->
          PolyAST.RDComp <$> renameRawDiagExpr tyVarNames tmVarNames mode a <*> renameRawDiagExpr tyVarNames tmVarNames mode b
        PolyAST.RDTensor a b ->
          PolyAST.RDTensor <$> renameRawDiagExpr tyVarNames tmVarNames mode a <*> renameRawDiagExpr tyVarNames tmVarNames mode b

    renameRawBinderArg tyVarNames tmVarNames mode barg =
      case barg of
        PolyAST.RBAExpr d ->
          PolyAST.RBAExpr <$> renameRawDiagExpr tyVarNames tmVarNames mode d
        PolyAST.RBAMeta name ->
          Right (PolyAST.RBAMeta name)

    renameRawTypeAsType tyVarNames tmVarNames mode ty =
      case ty of
        PolyAST.RPTVar name ->
          if name `S.member` tyVarNames
            then Right (PolyAST.RPTVar name)
            else do
              ref <- resolveRawTypeRefAsType mode (PolyAST.RawTypeRef Nothing name)
              let ref0 = M.findWithDefault ref ref tyRen
              let ref' = ref0 { orMode = renameModeName modeRen (orMode ref0) }
              pure (mkQualifiedRawTypeCon ref' [])
        PolyAST.RPTCon ref args ->
          case asModalityCall mode ref args of
            Just (rawMe, innerRaw) -> do
              (srcMode, _tgtMode) <- rawModExprEndpoints mode rawMe
              inner' <- renameRawTypeAsType tyVarNames tmVarNames srcMode innerRaw
              let rawMe' = renameRawModExpr rawMe
              pure (PolyAST.RPTMod rawMe' inner')
            Nothing -> do
              ref0 <- resolveRawTypeRefAsType mode ref
              tables <- ctorTablesByDoc
              sig <- lookupCtorSigForOwnerInTables doc tables mode ref0
              if length (sig) /= length args
                then Left "poly pushout: obligation raw type arity mismatch"
                else do
                  args0 <- mapM (renameOneArg tyVarNames tmVarNames) (zip (sig) args)
                  let args1 =
                        case M.lookup ref0 permRen of
                          Nothing -> Right args0
                          Just perm -> applyPerm perm args0
                  args2 <- args1
                  let ref1 = M.findWithDefault ref0 ref0 tyRen
                  let ref' = ref1 { orMode = renameModeName modeRen (orMode ref1) }
                  pure (mkQualifiedRawTypeCon ref' args2)
        PolyAST.RPTMod me inner -> do
          (innerMode, _outerMode) <- rawModExprEndpoints mode me
          inner' <- renameRawTypeAsType tyVarNames tmVarNames innerMode inner
          let me' = renameRawModExpr me
          pure (PolyAST.RPTMod me' inner')

    renameRawTypeAsTmTerm tmVarNames mode ty =
      case ty of
        PolyAST.RPTVar name ->
          if name `S.member` tmVarNames
            then Right (PolyAST.RPTVar name)
            else do
              let name' = renameTmFunLike mode name
              Right (PolyAST.RPTVar name')
        PolyAST.RPTCon ref args -> do
          args' <- mapM (renameRawTypeAsTmTerm tmVarNames mode) args
          let name' = renameTmFunLike mode (PolyAST.rtrName ref)
          pure
            ( PolyAST.RPTCon
                ref
                  { PolyAST.rtrName = name'
                  }
                args'
            )
        PolyAST.RPTMod _ _ ->
          Left "poly pushout: modality application is invalid in term-argument context"

    renameRawGenArgs tyVarNames tmVarNames mode genName mArgs =
      case mArgs of
        Nothing -> Right Nothing
        Just args -> do
          genDecl <- lookupGenDecl mode genName
          let paramKinds =
                [ case gp of
                    GP_Ty v -> Left v
                    GP_Tm v -> Right v
                | gp <- gdParams genDecl
                ]
          if length args > length paramKinds
            then Left "poly pushout: obligation raw generator argument mismatch"
            else do
              args' <- mapM (renameGenArg tyVarNames tmVarNames mode) (zip args (take (length args) paramKinds))
              Right (Just args')

    renameGenArg tyVarNames tmVarNames mode (arg, kind) =
      case kind of
        Left _ ->
          renameRawTypeAsType tyVarNames tmVarNames mode arg
        Right tmv ->
          renameRawTypeAsTmTerm tmVarNames (objMode (tmvSort tmv)) arg

    renameOneArg tyVarNames tmVarNames (param, arg) =
      case param of
        TPS_Ty mode ->
          renameRawTypeAsType tyVarNames tmVarNames mode arg
        TPS_Tm sortTy ->
          renameRawTypeAsTmTerm tmVarNames (objMode sortTy) arg

    lookupGenDecl mode genName =
      case M.lookup mode (dGens doc) >>= M.lookup genName of
        Nothing -> Left "poly pushout: obligation raw diagram references unknown generator"
        Just gd -> Right gd

    resolveRawTypeRefAsType ownerMode rawRef =
      case PolyAST.rtrMode rawRef of
        Just modeTxt -> do
          let qualifier = ModeName modeTxt
          let tname = ObjName (PolyAST.rtrName rawRef)
          tables <- ctorTablesByDoc
          let mRef = lookupCtorRefForOwnerInTables doc tables ownerMode tname
          case mRef of
            Just ref
              | orMode ref == qualifier -> Right ref
              | otherwise -> Left "poly pushout: obligation raw type references unknown qualified type"
            Nothing -> Left "poly pushout: obligation raw type references unknown qualified type"
        Nothing -> do
          let tname = ObjName (PolyAST.rtrName rawRef)
          tables <- ctorTablesByDoc
          let mRef = lookupCtorRefForOwnerInTables doc tables ownerMode tname
          case mRef of
            Nothing -> Left "poly pushout: obligation raw type references unknown type"
            Just ref -> Right ref

    asModalityCall ownerMode rawRef args =
      case (PolyAST.rtrMode rawRef, PolyAST.rtrName rawRef, args) of
        (Nothing, name, [inner]) ->
          if hasModality name
            then Just (PolyAST.RMComp [name], inner)
            else Nothing
        (Just modeTok, name, [inner]) ->
          if hasQualifiedType ownerMode modeTok name
            then Nothing
            else
              if hasModality modeTok && hasModality name
                then Just (PolyAST.RMComp [modeTok, name], inner)
                else Nothing
        _ -> Nothing

    hasModality tok =
      M.member (ModName tok) (mtDecls mt)

    hasQualifiedType ownerMode modeTok tyTok =
      case ctorTablesByDoc of
        Right tables ->
          case lookupCtorRefForOwnerInTables doc tables ownerMode (ObjName tyTok) of
            Just ref -> orMode ref == ModeName modeTok
            Nothing -> False
        Left _ -> False

    renameTmFunLike mode name =
      let genName = GenName name
          genName' = M.findWithDefault genName (mode, genName) genRen
      in renderGenName genName'

    mkQualifiedRawTypeCon ref args =
      PolyAST.RPTCon
        PolyAST.RawTypeRef
          { PolyAST.rtrMode = Just (renderModeName (orMode ref))
          , PolyAST.rtrName = renderTypeName (orName ref)
          }
        args

    rawModExprEndpoints fallbackMode me =
      case me of
        PolyAST.RMId modeNameTxt ->
          let modeName = ModeName modeNameTxt
          in if M.member modeName (mtModes mt)
            then Right (modeName, modeName)
            else Left "poly pushout: obligation raw modality references unknown mode"
        PolyAST.RMComp [] ->
          Right (fallbackMode, fallbackMode)
        PolyAST.RMComp (tok:toks) -> do
          firstDecl <- lookupRawMod tok
          (_cur, out) <- foldM step (mdSrc firstDecl, mdTgt firstDecl) toks
          pure (mdSrc firstDecl, out)
          where
            step (_curIn, curOut) tok' = do
              decl <- lookupRawMod tok'
              if mdSrc decl == curOut
                then Right (curOut, mdTgt decl)
                else Left "poly pushout: obligation raw modality composition type mismatch"

    lookupRawMod tok =
      case M.lookup (ModName tok) (mtDecls mt) of
        Nothing -> Left "poly pushout: obligation raw modality references unknown modality"
        Just decl -> Right decl

    renderModeName (ModeName t) = t
    renderTypeName (ObjName t) = t
    renderGenName (GenName t) = t

renameCell
  :: M.Map ModeName ModeName
  -> M.Map ModName ModName
  -> AttrSortRenameMap
  -> TypeRenameMap
  -> TypePermMap
  -> M.Map (ModeName, GenName) GenName
  -> M.Map (ModeName, Text) Text
  -> Cell2
  -> Either Text Cell2
renameCell modeRen modRen attrRen tyRen permRen genRen cellRen cell = do
  let mode = dMode (c2LHS cell)
  let name' = M.findWithDefault (c2Name cell) (mode, c2Name cell) cellRen
  lhs' <- renameDiagram modeRen modRen attrRen tyRen permRen genRen (c2LHS cell)
  rhs' <- renameDiagram modeRen modRen attrRen tyRen permRen genRen (c2RHS cell)
  pure cell
    { c2Name = name'
    , c2LHS = lhs'
    , c2RHS = rhs'
    }

renameDiagram
  :: M.Map ModeName ModeName
  -> M.Map ModName ModName
  -> AttrSortRenameMap
  -> TypeRenameMap
  -> TypePermMap
  -> M.Map (ModeName, GenName) GenName
  -> Diagram
  -> Either Text Diagram
renameDiagram modeRen modRen attrRen tyRen permRen genRen diag =
  traverseDiagram onDiag onPayload pure diag
  where
    mode = dMode diag

    onDiag d = do
      dTmCtx' <- mapM (renameObjExpr modeRen modRen tyRen permRen) (dTmCtx d)
      dPortObj' <- traverse (renameObjExpr modeRen modRen tyRen permRen) (dPortObj d)
      pure d
        { dMode = renameModeName modeRen (dMode d)
        , dTmCtx = dTmCtx'
        , dPortObj = dPortObj'
        }

    onPayload payload =
      case payload of
        PGen gen attrs bargs -> do
          let gen' = M.findWithDefault gen (mode, gen) genRen
              attrs' = M.map (renameAttrSortTerm attrRen) attrs
          bargs' <- mapM renameBinderArg bargs
          pure (PGen gen' attrs' bargs')
        PTmMeta v -> do
          sort' <- renameObjExpr modeRen modRen tyRen permRen (tmvSort v)
          pure (PTmMeta v { tmvSort = sort' })
        _ -> pure payload

    renameBinderArg barg =
      case barg of
        BAConcrete d ->
          BAConcrete <$> renameDiagram modeRen modRen attrRen tyRen permRen genRen d
        BAMeta x -> Right (BAMeta x)

renameAttrSortTerm :: AttrSortRenameMap -> AttrTerm -> AttrTerm
renameAttrSortTerm ren term =
  case term of
    ATLit lit -> ATLit lit
    ATVar v ->
      let sortName' = M.findWithDefault (avSort v) (avSort v) ren
      in ATVar v { avSort = sortName' }

renameInputShape
  :: M.Map ModeName ModeName
  -> M.Map ModName ModName
  -> TypeRenameMap
  -> TypePermMap
  -> InputShape
  -> Either Text InputShape
renameInputShape modeRen modRen ren permRen shape =
  case shape of
    InPort ty -> InPort <$> renameObjExpr modeRen modRen ren permRen ty
    InBinder bs -> InBinder <$> renameBinderSig modeRen modRen ren permRen bs

renameBinderSig
  :: M.Map ModeName ModeName
  -> M.Map ModName ModName
  -> TypeRenameMap
  -> TypePermMap
  -> BinderSig
  -> Either Text BinderSig
renameBinderSig modeRen modRen ren permRen sig = do
  tmCtx' <- mapM (renameObjExpr modeRen modRen ren permRen) (bsTmCtx sig)
  dom' <- mapM (renameObjExpr modeRen modRen ren permRen) (bsDom sig)
  cod' <- mapM (renameObjExpr modeRen modRen ren permRen) (bsCod sig)
  pure sig { bsTmCtx = tmCtx', bsDom = dom', bsCod = cod' }

renameObjExpr
  :: M.Map ModeName ModeName
  -> M.Map ModName ModName
  -> TypeRenameMap
  -> TypePermMap
  -> Obj
  -> Either Text Obj
renameObjExpr modeRen modRen ren permRen ty = do
  code' <- renameCode (objCode ty)
  let owner' = renameModeName modeRen (objOwnerMode ty)
  Right Obj { objOwnerMode = owner', objCode = code' }
  where
    renameCode code =
      case code of
        CTMeta v -> do
          sort' <- renameObjExpr modeRen modRen ren permRen (tmvSort v)
          Right (CTMeta v { tmvSort = sort', tmvOwnerMode = fmap (renameModeName modeRen) (tmvOwnerMode v) })
        CTMod me inner -> do
          inner' <- renameCode inner
          Right (CTMod (renameModExpr modeRen modRen me) inner')
        CTLift me inner -> do
          inner' <- renameCode inner
          Right (CTLift (renameModExpr modeRen modRen me) inner')
        CTCon ref args -> do
          args' <- mapM renameArg args
          let ref1 = M.findWithDefault ref ref ren
          let ref' = ref1 { orMode = renameModeName modeRen (orMode ref1) }
          case M.lookup ref permRen of
            Nothing -> Right (CTCon ref' args')
            Just perm -> do
              args'' <- applyPerm perm args'
              Right (CTCon ref' args'')

    renameArg arg =
      case arg of
        OAObj t -> OAObj <$> renameObjExpr modeRen modRen ren permRen t
        OATm tmArg -> OATm <$> renameTermDiagram tmArg

    renameTermDiagram (TermDiagram diag) = do
      let tmCtx' = mapM (renameObjExpr modeRen modRen ren permRen) (dTmCtx diag)
      let portTy' = mapM (renameObjExpr modeRen modRen ren permRen) (dPortObj diag)
      tmCtx <- tmCtx'
      portTy <- portTy'
      edges <- mapM renameEdge (dEdges diag)
      Right
        ( TermDiagram
            diag
              { dMode = renameModeName modeRen (dMode diag)
              , dTmCtx = tmCtx
              , dPortObj = portTy
              , dEdges = edges
              }
        )

    renameEdge edge =
      case ePayload edge of
        PTmMeta v -> do
          sort' <- renameObjExpr modeRen modRen ren permRen (tmvSort v)
          Right edge { ePayload = PTmMeta v { tmvSort = sort' } }
        _ -> Right edge

applyPerm :: [Int] -> [a] -> Either Text [a]
applyPerm perm args
  | length perm /= n = Left "poly pushout: type permutation arity mismatch"
  | any outOfRange perm = Left "poly pushout: type permutation position out of range"
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
  ensureModeTheory "left" a
  ensureModeTheory "right" b
  attrSorts <- mergeAttrSorts (dAttrSorts a) (dAttrSorts b)
  gens <- mergeGenTables (dGens a) (dGens b)
  cells <- mergeCells mt (dCells2 a) (dCells2 b)
  actions <- mergeActions (dActions a) (dActions b)
  obligations <- mergeObligations (dObligations a) (dObligations b)
  let merged =
        a
          { dModes = mt
          , dAcyclicModes = S.union (dAcyclicModes a) (dAcyclicModes b)
          , dAttrSorts = attrSorts
          , dGens = gens
          , dCells2 = cells
          , dActions = actions
          , dObligations = obligations
          }
  validateDoctrine merged
  pure merged
  where
    ensureModeTheory side doc =
      if dModes doc == mt
        then Right ()
        else Left ("poly pushout: " <> side <> " doctrine mode theory mismatch")

    mergeAttrSorts left right =
      foldl add (Right left) (M.toList right)
      where
        add acc (name, decl) = do
          mp <- acc
          case M.lookup name mp of
            Nothing -> Right (M.insert name decl mp)
            Just existing | existing == decl -> Right mp
            _ -> Left "poly pushout: attribute sort conflict"
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

    mergeActions left right =
      foldl add (Right left) (M.toList right)
      where
        add acc (modName, act) = do
          mp <- acc
          case M.lookup modName mp of
            Nothing -> Right (M.insert modName act mp)
            Just existing
              | existing == act -> Right mp
              | otherwise -> Left "poly pushout: modality action conflict"

    mergeObligations left right =
      foldl add (Right left) right
      where
        add acc obl = do
          obs <- acc
          case filter (\x -> obName x == obName obl) obs of
            [] -> Right (obs <> [obl])
            (existing:_)
              | existing == obl -> Right obs
              | otherwise -> Left "poly pushout: obligation conflict"

mergeCells :: ModeTheory -> [Cell2] -> [Cell2] -> Either Text [Cell2]
mergeCells mt left right =
  foldl insertCell (Right []) (left <> right)
  where
    cellScopedKey c = (dMode (c2LHS c), c2Name c)

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
      case filter (\c -> cellScopedKey c == cellScopedKey cell) cells of
        (c:_) -> Just c
        [] -> Nothing

    bodiesIso a b =
      case cellBodyEq a b of
        Left _ -> False
        Right ok -> ok

    replaceCell target newCell cells =
      let targetKey = cellScopedKey target
          (before, after) = break (\c -> cellScopedKey c == targetKey) cells
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
      else if length (c2TmVars a) /= length (c2TmVars b)
        then Right False
        else do
          b' <- alphaRenameCellTo (c2TyVars b) (c2TyVars a) (c2TmVars b) (c2TmVars a) b
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
    && length (gdTmVars g1) == length (gdTmVars g2)
    && let tyMap = M.fromList (zip (gdTyVars g2) (gdTyVars g1))
           tmMap = M.fromList (zip (gdTmVars g2) (gdTmVars g1))
           tyVars2 = map (renameTyVarAlpha tyMap) (gdTyVars g2)
           tmVars2 = map (renameTmVarAlpha tyMap tmMap) (gdTmVars g2)
           dom2 = map (renameInputShapeAlpha tyMap tmMap) (gdDom g2)
           cod2 = map (renameTypeAlpha tyMap tmMap) (gdCod g2)
       in tyVars2 == gdTyVars g1
            && tmVars2 == gdTmVars g1
            && dom2 == gdDom g1
            && cod2 == gdCod g1

genDeclAlphaEqIgnoringName :: GenDecl -> GenDecl -> Bool
genDeclAlphaEqIgnoringName g1 g2 =
  let shared = GenName "__cmp__"
  in genDeclAlphaEq (g1 { gdName = shared }) (g2 { gdName = shared })

alphaRenameCellTo :: [TmVar] -> [TmVar] -> [TmVar] -> [TmVar] -> Cell2 -> Either Text Cell2
alphaRenameCellTo fromTy toTy fromTm toTm cell
  | length fromTy /= length toTy = Left "poly pushout: alpha rename type arity mismatch"
  | length fromTm /= length toTm = Left "poly pushout: alpha rename term-variable arity mismatch"
  | otherwise =
      let tyMap = M.fromList (zip fromTy toTy)
          tmMap = M.fromList (zip fromTm toTm)
          lhs' = renameDiagramAlpha tyMap tmMap (c2LHS cell)
          rhs' = renameDiagramAlpha tyMap tmMap (c2RHS cell)
      in Right cell { c2TyVars = toTy, c2TmVars = toTm, c2LHS = lhs', c2RHS = rhs' }

renameTyVarAlpha :: M.Map TmVar TmVar -> TmVar -> TmVar
renameTyVarAlpha tyMap v =
  M.findWithDefault v v tyMap

renameTmVarAlpha :: M.Map TmVar TmVar -> M.Map TmVar TmVar -> TmVar -> TmVar
renameTmVarAlpha tyMap tmMap v =
  case M.lookup v tmMap of
    Just v' -> v'
    Nothing -> v { tmvSort = renameTypeAlpha tyMap tmMap (tmvSort v) }

renameTypeAlpha :: M.Map TmVar TmVar -> M.Map TmVar TmVar -> Obj -> Obj
renameTypeAlpha tyMap tmMap = mapObjExpr renameTy renameTm
  where
    renameTy ty =
      case ty of
        OVar v -> OVar (renameTyVarAlpha tyMap v)
        _ -> ty
    renameTm (TermDiagram diag) =
      TermDiagram $
        runIdentity $
          traverseDiagram onDiag onPayload pure diag
      where
        onDiag d =
          pure d
            { dPortObj = IM.map (renameTypeAlpha tyMap tmMap) (dPortObj d)
            , dTmCtx = map (renameTypeAlpha tyMap tmMap) (dTmCtx d)
            }
        onPayload payload =
          pure $
            case payload of
              PTmMeta v -> PTmMeta (renameTmVarAlpha tyMap tmMap v)
              _ -> payload

renameInputShapeAlpha :: M.Map TmVar TmVar -> M.Map TmVar TmVar -> InputShape -> InputShape
renameInputShapeAlpha tyMap tmMap shape =
  case shape of
    InPort ty -> InPort (renameTypeAlpha tyMap tmMap ty)
    InBinder bs ->
      let tmCtx' = map (renameTypeAlpha tyMap tmMap) (bsTmCtx bs)
          dom' = map (renameTypeAlpha tyMap tmMap) (bsDom bs)
          cod' = map (renameTypeAlpha tyMap tmMap) (bsCod bs)
      in InBinder bs { bsTmCtx = tmCtx', bsDom = dom', bsCod = cod' }

renameDiagramAlpha :: M.Map TmVar TmVar -> M.Map TmVar TmVar -> Diagram -> Diagram
renameDiagramAlpha tyMap tmMap =
  runIdentity . traverseDiagram onDiag pure pure
  where
    onDiag d =
      pure d
        { dTmCtx = map (renameTypeAlpha tyMap tmMap) (dTmCtx d)
        , dPortObj = IM.map (renameTypeAlpha tyMap tmMap) (dPortObj d)
        }

normalizeDiagramModes :: ModeTheory -> Diagram -> Either Text Diagram
normalizeDiagramModes mt diag = do
  tmCtx' <- mapM normalizeTypeModes (dTmCtx diag)
  portTy' <- traverse normalizeTypeModes (dPortObj diag)
  edges' <- traverse normalizeEdgeModes (dEdges diag)
  pure diag { dTmCtx = tmCtx', dPortObj = portTy', dEdges = edges' }
  where
    normalizeEdgeModes edge =
      case ePayload edge of
        PGen g attrs bargs -> do
          bargs' <- mapM normalizeBinderArg bargs
          pure edge { ePayload = PGen g attrs bargs' }
        PBox name inner -> do
          inner' <- normalizeDiagramModes mt inner
          pure edge { ePayload = PBox name inner' }
        PFeedback inner -> do
          inner' <- normalizeDiagramModes mt inner
          pure edge { ePayload = PFeedback inner' }
        PSplice x ->
          pure edge { ePayload = PSplice x }
        PTmMeta v -> do
          sort' <- normalizeTypeModes (tmvSort v)
          pure edge { ePayload = PTmMeta v { tmvSort = sort' } }
        PInternalDrop ->
          pure edge { ePayload = PInternalDrop }

    normalizeBinderArg barg =
      case barg of
        BAConcrete inner -> BAConcrete <$> normalizeDiagramModes mt inner
        BAMeta x -> Right (BAMeta x)

    normalizeTypeModes ty = do
      ty' <- goType ty
      normalizeObjExpr mt ty'

    goType ty =
      case objCode ty of
        CTMeta _ -> Right ty
        CTCon ref args -> do
          args' <- mapM goArg args
          Right ty { objCode = CTCon ref args' }
        CTMod me innerCode -> do
          inner' <- goType Obj { objOwnerMode = meSrc me, objCode = innerCode }
          Right ty { objCode = CTMod me (objCode inner') }
        CTLift me innerCode -> do
          inner' <- goType Obj { objOwnerMode = meSrc me, objCode = innerCode }
          Right ty { objCode = CTLift me (objCode inner') }

    goArg arg =
      case arg of
        OAObj ty -> OAObj <$> goType ty
        OATm tmArg -> OATm <$> goTm tmArg

    goTm (TermDiagram diag) = do
      tmCtx' <- mapM goType (dTmCtx diag)
      portTy' <- mapM goType (dPortObj diag)
      edges' <- mapM goEdge (dEdges diag)
      Right
        ( TermDiagram
            diag
              { dTmCtx = tmCtx'
              , dPortObj = portTy'
              , dEdges = edges'
              }
        )

    goEdge edge =
      case ePayload edge of
        PTmMeta v -> do
          sort' <- goType (tmvSort v)
          Right edge { ePayload = PTmMeta v { tmvSort = sort' } }
        _ -> Right edge

buildInj
  :: Text
  -> Doctrine
  -> Doctrine
  -> M.Map ModeName ModeName
  -> M.Map ModName ModName
  -> AttrSortRenameMap
  -> TypeRenameMap
  -> TypePermMap
  -> M.Map (ModeName, GenName) GenName
  -> Either Text Morphism
buildInj name src tgt modeRen modRen attrRen tyRen permRen genRen = do
  srcCtorTables <- deriveCtorTables src
  attrSortMap <- buildAttrSortMap src attrRen
  typeMap <- buildTypeMap srcCtorTables src tgt modeRen modRen tyRen permRen
  genMap <- buildGenMap srcCtorTables src tgt modeRen modRen attrRen tyRen permRen genRen
  pure Morphism
    { morName = name
    , morSrc = src
    , morTgt = tgt
    , morIsCoercion = True
    , morModeMap = buildModeMap src modeRen
    , morModMap = buildModMap src modeRen modRen
    , morAttrSortMap = attrSortMap
    , morTypeMap = typeMap
    , morGenMap = genMap
    , morCheck = CheckAll
    , morPolicy = UseOnlyComputationalLR
    }

buildModeMap :: Doctrine -> M.Map ModeName ModeName -> M.Map ModeName ModeName
buildModeMap src ren =
  M.fromList
    [ (mode, renameModeName ren mode)
    | mode <- M.keys (mtModes (dModes src))
    ]

buildModMap :: Doctrine -> M.Map ModeName ModeName -> M.Map ModName ModName -> M.Map ModName ModExpr
buildModMap src modeRen modRen =
  M.fromList
    [ (name, image decl)
    | (name, decl) <- M.toList (mtDecls (dModes src))
    ]
  where
    image decl =
      ModExpr
        { meSrc = renameModeName modeRen (mdSrc decl)
        , meTgt = renameModeName modeRen (mdTgt decl)
        , mePath = [renameModName modRen (mdName decl)]
        }

buildAttrSortMap :: Doctrine -> AttrSortRenameMap -> Either Text (M.Map AttrSort AttrSort)
buildAttrSortMap doc renames =
  foldM add M.empty (M.keys (dAttrSorts doc))
  where
    add mp srcSort =
      let tgtSort = M.findWithDefault srcSort srcSort renames
      in Right (M.insert srcSort tgtSort mp)

buildTypeMap
  :: CtorTables
  -> Doctrine
  -> Doctrine
  -> M.Map ModeName ModeName
  -> M.Map ModName ModName
  -> TypeRenameMap
  -> TypePermMap
  -> Either Text (M.Map ObjRef TypeTemplate)
buildTypeMap srcCtorTables srcDoc tgtDoc modeRen modRen renames permRen = do
  ttTgt <- doctrineTypeTheory tgtDoc
  srcCtors <- allCtorsInTables srcDoc srcCtorTables
  foldM (add ttTgt) M.empty srcCtors
  where
    add ttTgt mp (ref, sig) = do
      let ref0 = M.findWithDefault ref ref renames
      let ref' = ref0 { orMode = renameModeName modeRen (orMode ref0) }
      let mPerm = M.lookup ref permRen
      if ref' == ref && mPerm == Nothing
        then Right mp
        else do
          tmpl <- renameTemplate ttTgt ref' mPerm (sig)
          Right (M.insert ref tmpl mp)
    renameTemplate ttTgt tgtRef mPerm params = do
      tmplParams <- mapM mkParam (zip [0 :: Int ..] params)
      args0 <- mapM (toArg ttTgt) (zip params tmplParams)
      args <- case mPerm of
        Nothing -> Right args0
        Just perm -> applyPerm perm args0
      pure (TypeTemplate tmplParams (mkCon tgtRef args))

    mkParam (i, param) =
      case param of
        TPS_Ty mode -> do
          v <- mkTypeMetaVarForMode tgtDoc (renameModeName modeRen mode) ("a" <> T.pack (show i))
          Right (TPType v)
        TPS_Tm sortTy -> do
          sortTy' <- renameObjExpr modeRen modRen renames permRen sortTy
          Right (TPTm TmVar { tmvName = "i" <> T.pack (show i), tmvSort = sortTy', tmvScope = 0, tmvOwnerMode = Nothing })

    toArg tt (srcParam, param) =
      case (srcParam, param) of
        (TPS_Ty ownerMode, TPType v) ->
          Right (OAObj Obj { objOwnerMode = renameModeName modeRen ownerMode, objCode = CTMeta v })
        (TPS_Tm _, TPType _) ->
          Left "poly pushout: internal kind mismatch for type template argument"
        (_, TPTm v) -> do
          tm <- termExprToDiagramChecked tt [] (tmvSort v) (TMVar v)
          Right (OATm tm)

buildGenMap
  :: CtorTables
  -> Doctrine
  -> Doctrine
  -> M.Map ModeName ModeName
  -> M.Map ModName ModName
  -> AttrSortRenameMap
  -> TypeRenameMap
  -> TypePermMap
  -> M.Map (ModeName, GenName) GenName
  -> Either Text (M.Map (ModeName, GenName) GenImage)
buildGenMap srcCtorTables src tgt modeRen modRen attrRen tyRen permRen genRen =
  do
    let srcGens = allGensInTables src srcCtorTables
    fmap M.fromList (mapM build srcGens)
  where
    build (mode, gen) = do
      let genName = gdName gen
      let mode' = renameModeName modeRen mode
      let genName' = M.findWithDefault genName (mode, genName) genRen
      dom <- mapM (renameObjExpr modeRen modRen tyRen permRen) (gdPlainDom gen)
      cod <- mapM (renameObjExpr modeRen modRen tyRen permRen) (gdCod gen)
      _ <- ensureGenExists tgt mode' genName'
      let attrs =
            M.fromList
              [ (fieldName, ATVar (AttrVar fieldName (M.findWithDefault sortName sortName attrRen)))
              | (fieldName, sortName) <- gdAttrs gen
              ]
      d0 <- genDWithAttrs mode' dom cod genName' attrs
      let binderSlots = [ bs | InBinder bs <- gdDom gen ]
      binderSlotsRenamed <- mapM (renameBinderSig modeRen modRen tyRen permRen) binderSlots
      let holes = [ BinderMetaVar ("b" <> T.pack (show i)) | i <- [0 .. length binderSlots - 1] ]
      let bargs = map BAMeta holes
      let binderSigs = M.fromList (zip holes binderSlotsRenamed)
      d <- setSingleGenBargs genName' attrs bargs d0
      pure ((mode, genName), GenImage d binderSigs)

    setSingleGenBargs genName attrs bargs diag =
      case IM.toList (dEdges diag) of
        [(edgeKey, edge)] ->
          let edge' = edge { ePayload = PGen genName attrs bargs }
          in Right diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
        _ -> Left "poly pushout: generated image is not a single generator edge"

composeMorphisms :: Text -> Morphism -> Morphism -> Either Text Morphism
composeMorphisms name first second = do
  if morTgt first /= morSrc second
    then Left "poly pushout: morphism composition boundary mismatch"
    else Right ()
  modeMap <- composeModeMap
  modMap <- composeModMap
  attrMap <- composeAttrSortMap
  typeMap <- composeTypeMap
  genMap <- composeGenMap
  pure
    Morphism
      { morName = name
      , morSrc = morSrc first
      , morTgt = morTgt second
      , morIsCoercion = morIsCoercion first && morIsCoercion second
      , morModeMap = modeMap
      , morModMap = modMap
      , morAttrSortMap = attrMap
      , morTypeMap = typeMap
      , morGenMap = genMap
      , morCheck = morCheck first
      , morPolicy = morPolicy first
      }
  where
    composeModeMap =
      fmap M.fromList $
        mapM oneMode (M.keys (mtModes (dModes (morSrc first))))
      where
        oneMode modeSrc = do
          modeMid <- applyMorphismMode first modeSrc
          modeTgt <- applyMorphismMode second modeMid
          Right (modeSrc, modeTgt)

    composeModMap =
      fmap M.fromList $
        mapM oneMod (M.keys (mtDecls (dModes (morSrc first))))
      where
        oneMod modName = do
          meMid <-
            case M.lookup modName (morModMap first) of
              Nothing -> Left "poly pushout: missing modality image during morphism composition"
              Just me -> Right me
          meTgt <- applyMorphismModExpr second meMid
          Right (modName, meTgt)

    composeAttrSortMap =
      fmap M.fromList $
        mapM oneAttrSort (M.keys (dAttrSorts (morSrc first)))
      where
        oneAttrSort srcSort = do
          midSort <-
            case M.lookup srcSort (morAttrSortMap first) of
              Nothing -> Left "poly pushout: missing attrsort image during morphism composition"
              Just out -> Right out
          tgtSort <-
            case M.lookup midSort (morAttrSortMap second) of
              Nothing -> Left "poly pushout: missing composed attrsort image during morphism composition"
              Just out -> Right out
          Right (srcSort, tgtSort)

    composeTypeMap = do
      srcCtorTables <- deriveCtorTables (morSrc first)
      ttSrc <- doctrineTypeTheoryFromTables (morSrc first) srcCtorTables
      firstTgtCtorTables <- deriveCtorTables (morTgt first)
      secondTgtCtorTables <- deriveCtorTables (morTgt second)
      srcCtors <- allCtorsInTables (morSrc first) srcCtorTables
      fmap M.fromList (mapM (oneType ttSrc firstTgtCtorTables secondTgtCtorTables) srcCtors)
      where
        oneType ttSrc firstTgtCtorTables secondTgtCtorTables (srcRef, sig) = do
          paramsSrc <- mapM (mkSourceParam sig) (zip [0 :: Int ..] (sig))
          argsSrc <- mapM (sourceParamArg ttSrc) (zip (sig) paramsSrc)
          let tySrc = mkCon srcRef argsSrc
          tyMid <- applyMorphismTyWithTables firstTgtCtorTables first tySrc
          tyTgt <- applyMorphismTyWithTables secondTgtCtorTables second tyMid
          paramsTgt <- mapM (mapComposedParam firstTgtCtorTables secondTgtCtorTables) paramsSrc
          Right (srcRef, TypeTemplate paramsTgt tyTgt)

        mkSourceParam _sig (i, param) =
          case param of
            TPS_Ty mode -> do
              v <- mkTypeMetaVarForMode (morSrc first) mode ("a" <> T.pack (show i))
              Right (TPType v)
            TPS_Tm sortTy ->
              let tmVar =
                    TmVar
                      { tmvName = "t" <> T.pack (show i)
                      , tmvSort = sortTy
                      , tmvScope = 0
                      , tmvOwnerMode = Nothing
                      }
              in Right (TPTm tmVar)

        sourceParamArg ttSrc (srcParam, param) =
          case (srcParam, param) of
            (TPS_Ty ownerMode, TPType v) ->
              Right (OAObj Obj { objOwnerMode = ownerMode, objCode = CTMeta v })
            (TPS_Tm _, TPType _) ->
              Left "poly pushout: internal kind mismatch for composed type argument"
            (_, TPTm v) -> do
              tm <- termExprToDiagramChecked ttSrc [] (tmvSort v) (TMVar v)
              Right (OATm tm)

        mapComposedParam firstTgtCtorTables secondTgtCtorTables param =
          case param of
            TPType v -> do
              let ownerSrc = maybe (objOwnerMode (tmvSort v)) id (tmvOwnerMode v)
              ownerMid <- applyMorphismMode first ownerSrc
              ownerTgt <- applyMorphismMode second ownerMid
              sortMid <- applyMorphismTyWithTables firstTgtCtorTables first (tmvSort v)
              sortTgt <- applyMorphismTyWithTables secondTgtCtorTables second sortMid
              Right (TPType v { tmvSort = sortTgt, tmvOwnerMode = Just ownerTgt })
            TPTm v -> do
              sortMid <- applyMorphismTyWithTables firstTgtCtorTables first (tmvSort v)
              sortTgt <- applyMorphismTyWithTables secondTgtCtorTables second sortMid
              Right (TPTm v { tmvSort = sortTgt })

    composeGenMap = do
      secondTgtCtorTables <- deriveCtorTables (morTgt second)
      fmap M.fromList (mapM (oneGen secondTgtCtorTables) (M.toList (morGenMap first)))
      where
        oneGen secondTgtCtorTables (key, imageMid) = do
          let imageMidRenamed = renameGenImageOuterHoles imageMid
          diagTgt <- applyMorphismDiagramWithTables secondTgtCtorTables second (giDiagram imageMidRenamed)
          binderSigsTgt <- mapM (applyMorphismBinderSigWithTables secondTgtCtorTables second) (giBinderSigs imageMidRenamed)
          Right (key, GenImage diagTgt binderSigsTgt)

    renameGenImageOuterHoles image =
      let renHole (BinderMetaVar h) = BinderMetaVar ("compose_" <> h)
          renBinderArg barg =
            case barg of
              BAConcrete inner -> BAConcrete (renDiagram inner)
              BAMeta hole -> BAMeta (renHole hole)
          renPayload payload =
            case payload of
              PGen g attrs bargs -> PGen g attrs (map renBinderArg bargs)
              PBox nm inner -> PBox nm (renDiagram inner)
              PFeedback inner -> PFeedback (renDiagram inner)
              _ -> payload
          renDiagram =
            runIdentity . traverseDiagram pure (pure . renPayload) pure
          holeSigs' =
            M.fromList
              [ (renHole hole, sig)
              | (hole, sig) <- M.toList (giBinderSigs image)
              ]
      in image { giDiagram = renDiagram (giDiagram image), giBinderSigs = holeSigs' }

checkGenerated :: Text -> Morphism -> Either Text ()
checkGenerated label mor =
  case checkMorphism mor of
    Left err -> Left ("poly pushout generated morphism " <> label <> " invalid: " <> err)
    Right () -> Right ()

allCtorsInTables :: Doctrine -> CtorTables -> Either Text [(ObjRef, [TypeParamSig])]
allCtorsInTables doc tables = do
  merged <- foldM insertOwner M.empty (M.toList tables)
  pure (M.toList merged)
  where
    insertOwner acc (ownerMode, table) =
      let classifierMode = modeClassifierMode (dModes doc) ownerMode
       in foldM (insertCtor classifierMode) acc (M.toList table)

    insertCtor classifierMode acc (ctorName, sig) =
      let ref = ObjRef classifierMode ctorName
       in case M.lookup ref acc of
            Nothing -> Right (M.insert ref sig acc)
            Just sig0
              | sig0 == sig -> Right acc
              | otherwise -> Left "poly pushout: ambiguous constructor signature across owner modes"

lookupCtorSigByRefInTables :: Doctrine -> CtorTables -> ObjRef -> Either Text [TypeParamSig]
lookupCtorSigByRefInTables doc tables ref = do
  let sigs =
        [ sig
        | (ownerMode, table) <- M.toList tables
        , modeClassifierMode (dModes doc) ownerMode == orMode ref
        , Just sig <- [M.lookup (orName ref) table]
        ]
  case L.nub sigs of
    [] -> Left "poly pushout: target type missing"
    [sig] -> Right sig
    _ -> Left "poly pushout: ambiguous constructor signature across owner modes"

allGensInTables :: Doctrine -> CtorTables -> [(ModeName, GenDecl)]
allGensInTables doc tables =
  let ctorNamesByClassifier =
        M.fromListWith S.union
          [ (modeClassifierMode (dModes doc) ownerMode, S.fromList (M.keys table))
          | (ownerMode, table) <- M.toList tables
          ]
   in
    [ (mode, gen)
    | (mode, table) <- M.toList (dGens doc)
    , gen <- M.elems table
    , let GenName gName = gdName gen
    , let ctorNames = M.findWithDefault S.empty mode ctorNamesByClassifier
    , ObjName gName `S.notMember` ctorNames
    ]
