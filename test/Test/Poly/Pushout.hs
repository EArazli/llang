{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
module Test.Poly.Pushout
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.IntMap.Strict as IM
import qualified Strat.Poly.DSL.AST as PolyAST
import Strat.Poly.ModeTheory
  ( ModeName(..)
  , ModName(..)
  , ModExpr(..)
  , ModDecl(..)
  , ModEqn(..)
  , ModTransformName(..)
  , ModTransformDecl(..)
  , CompDecl(..)
  , ClassificationDecl(..)
  , ModeTheory(..)
  , ModeInfo(..)
  , DefEqEngine(..)
  , mtModes
  , mtDecls
  )
import Strat.Poly.Obj
  ( TmVar
  , tmvName
  , tmVarOwner
  , mkModeMetaVar
  , ObjName(..)
  , ObjRef(..)
  , Obj(..)
  , mkCon
  , ObjArg
  , pattern OAObj
  , pattern OATm
  , TmVar(..)
  , TermDiagram(..)
  , objMode
  )
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Diagram (genD, genDWithArgs, idD)
import Strat.Poly.Doctrine (Doctrine(..), GenDecl(..), GenParam(..), ModAction(..), ObligationDecl(..), InputShape(..), BinderSig(..), gdPlainDom, genericGenDiagram)
import qualified Strat.Poly.Doctrine as PolyDoc
import Strat.Poly.Cell2 (Cell2(..))
import Strat.Poly.Literal (LiteralKind(..))
import Strat.Poly.Morphism (Morphism(..), MorphismCheck(..), GenImage(..), TypeTemplate(..))
import qualified Strat.Poly.Morphism as PolyMor
import Strat.Poly.Pushout (PolyPushoutResult(..))
import qualified Strat.Poly.Pushout as PolyPush
import Strat.Poly.Graph (Diagram(..), BinderArg(..), BinderMetaVar(..), Edge(..), EdgePayload(..), emptyDiagram, freshPort, addEdgePayload)
import Strat.Poly.DiagramIso (diagramIsoEq)
import qualified Strat.Poly.DSL.Elab as PolyElab
import Strat.Poly.TypeTheory (TypeParamSig(..))
import Strat.Frontend.Env (emptyEnv)
import Strat.Common.Rules (RuleClass(..), Orientation(..), RewritePolicy(..))


tests :: TestTree
tests =
  testGroup
    "Poly.Pushout"
    [ testCase "pushout dedups equations by body" testPushoutDedupByBody
    , testCase "pushout type permutation commutes" testPushoutTypePermutationCommutes
    , testCase "pushout merges cell orientations" testPushoutMergeOrient
    , testCase "pushout merges cell classes" testPushoutMergeClass
    , testCase "pushout rejects name conflict with different bodies" testPushoutNameConflict
    , testCase "pushout accepts non-identity mode maps" testPushoutAcceptsModeMap
    , testCase "pushout keeps type refs in image modes under mode maps" testPushoutTypeRefsStayInPushoutModes
    , testCase "pushout disjoint cell renaming works with nontrivial mode renaming" testPushoutDisjointCellRenameUsesOriginalModeKey
    , testCase "pushout rejects mode collapse when comprehension witnesses diverge" testPushoutDisjointRenamesAfterModeCollapse
    , testCase "pushout allows same cell names in different modes" testPushoutCellNamesArePerMode
    , testCase "pushout allows compatible non-injective type maps" testPushoutNonInjectiveTypeCompatible
    , testCase "pushout rejects incompatible non-injective literal-kind maps" testPushoutNonInjectiveLiteralKindIncompatible
    , testCase "pushout allows compatible non-injective generator maps" testPushoutNonInjectiveGenCompatible
    , testCase "pushout rejects incompatible non-injective generator maps" testPushoutNonInjectiveGenIncompatible
    , testCase "pushout glue composes through right injection" testPushoutGlueComposesThroughInr
    , testCase "pushout generator injectivity is mode-aware" testPushoutGenInjectiveByMode
    , testCase "pushout default type rename follows mode map" testPushoutTypeRenameDefaultUsesModeMap
    , testCase "pushout classifiedBy universes follow type renames" testPushoutClassificationUniverseFollowsTypeRename
    , testCase "pushout rejects incompatible classified universes" testPushoutRejectsIncompatibleClassifiedUniverses
    , testCase "pushout accepts definitional-equal classified universes" testPushoutAcceptsDefEqClassifiedUniverses
    , testCase "pushout handles alpha-renaming with mode equations" testPushoutAlphaRenameWithModeEq
    , testCase "pushout supports term-parameterized type maps" testPushoutTermTypeMaps
    , testCase "pushout permutes mixed type/term parameters and renames term sorts" testPushoutTypePermutationSortRename
    , testCase "pushout merges cells alpha-equivalent over term vars" testPushoutCellTmAlphaEq
    , testCase "pushout injection morphism preserves concrete binder arguments" testPushoutInjectionPreservesBinderArgs
    , testCase "pushout accepts renaming morphisms with binder signatures in target doctrine" testPushoutAcceptsRenamingWithBinders
    , testCase "coproduct merges distinct mode theories" testCoproductMergesDistinctModeTheories
    , testCase "coproduct keeps obligations elaboratable after disjoint type renaming" testCoproductObligationRenameElaborates
    , testCase "coproduct renames raw modality obligation syntax under collisions" testCoproductObligationRawModalityRenameElaborates
    , testCase "coproduct renames colliding modality transforms" testCoproductTransformCollisionRenames
    , testCase "apply pushout accepts implementation morphisms with non-CheckAll checks" testApplyPushoutAcceptsNonCheckAllGlue
    , testCase "apply pushout rejects mode collapse when comprehension witnesses diverge" testApplyPushoutTypeGenCollisionAfterModeRename
    , testCase "apply pushout rejects colliding mode renames with comprehension mismatch" testApplyPushoutCellCollisionAfterModeRename
    , testCase "apply pushout accepts mode-collapse universes equal up to defeq" testApplyPushoutModeCollapseUniverseDefEq
    ]

require :: Either Text a -> IO a
require = either (assertFailure . T.unpack) pure

requireCell :: Doctrine -> Text -> IO Cell2
requireCell doc cellName =
  case [ cell | cell <- dCells2 doc, c2Name cell == cellName ] of
    [cell] -> pure cell
    [] -> assertFailure ("missing cell: " <> T.unpack cellName) >> fail "unreachable"
    _ -> assertFailure ("duplicate cell: " <> T.unpack cellName) >> fail "unreachable"

plainImage :: Diagram -> GenImage
plainImage diag = GenImage diag M.empty

identityGenImage :: GenDecl -> Either Text GenImage
identityGenImage gd = do
  diag <- genericGenDiagram gd
  let binderSlots = [bs | InBinder bs <- gdDom gd]
      holes = [BinderMetaVar ("b" <> T.pack (show i)) | i <- [0 :: Int .. length binderSlots - 1]]
  pure (GenImage diag (M.fromList (zip holes binderSlots)))

mappedIdentityGenImage :: Morphism -> GenDecl -> Either Text GenImage
mappedIdentityGenImage mor gd = do
  mode' <- PolyMor.applyMorphismMode mor (gdMode gd)
  dom' <- mapM (applyMorphismTy mor) (gdPlainDom gd)
  cod' <- mapM (applyMorphismTy mor) (gdCod gd)
  args <- mapM mapParam (gdParams gd)
  diag <- genDWithArgs mode' dom' cod' (gdName gd) args
  pure (GenImage diag M.empty)
  where
    mapParam param =
      case param of
        GP_Ty v -> do
          owner' <- PolyMor.applyMorphismMode mor (tmVarOwner v)
          sort' <- applyMorphismTy mor (tmvSort v)
          pure (OAObj (OVar v { tmvSort = sort', tmvOwnerMode = Just owner' }))
        GP_Tm v -> do
          sort' <- applyMorphismTy mor (tmvSort v)
          pure (OATm (tmMeta v { tmvSort = sort', tmvOwnerMode = Nothing }))

setSingleEdgeBargs :: Diagram -> [BinderArg] -> Either Text Diagram
setSingleEdgeBargs diag bargs =
  case IM.toList (dEdges diag) of
    [(edgeKey, edge@(Edge _ (PGen g args _) _ _))] ->
      let edge' = edge { ePayload = PGen g args bargs }
      in pure diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
    _ -> Left "expected a single generator edge"

tvar :: ModeName -> Text -> TmVar
tvar mode name = mkModeMetaVar name mode

tcon :: ModeName -> Text -> [Obj] -> Obj
tcon mode name args = mkCon (ObjRef mode (ObjName name)) (map OAObj args)

tmMeta :: TmVar -> TermDiagram
tmMeta v =
  let mode = objMode (tmvSort v)
      (outPid, d0) = freshPort (tmvSort v) (emptyDiagram mode [])
      d1 =
        case addEdgePayload (PTmMeta v) [] [outPid] d0 of
          Left err -> error (T.unpack err)
          Right d -> d
  in TermDiagram d1 { dOut = [outPid] }

identityModeMap :: Doctrine -> M.Map ModeName ModeName
identityModeMap doc =
  M.fromList [ (m, m) | m <- M.keys (mtModes (dModes doc)) ]

identityModMap :: Doctrine -> M.Map ModName ModExpr
identityModMap doc =
  M.fromList
    [ (name, ModExpr { meSrc = mdSrc decl, meTgt = mdTgt decl, mePath = [name] })
    | (name, decl) <- M.toList (mtDecls (dModes doc))
    ]

normalizeDoctrine :: Doctrine -> Doctrine
normalizeDoctrine = id

normalizeMorphism :: Morphism -> Morphism
normalizeMorphism mor =
  mor
    { morSrc = normalizeDoctrine (morSrc mor)
    , morTgt = normalizeDoctrine (morTgt mor)
    }

validateDoctrine :: Doctrine -> Either Text ()
validateDoctrine = PolyDoc.validateDoctrine . normalizeDoctrine

applyMorphismDiagram :: Morphism -> Diagram -> Either Text Diagram
applyMorphismDiagram mor = PolyMor.applyMorphismDiagram (normalizeMorphism mor)

applyMorphismTy :: Morphism -> Obj -> Either Text Obj
applyMorphismTy mor = PolyMor.applyMorphismTy (normalizeMorphism mor)

completeCompSupportMappings :: Morphism -> Either Text Morphism
completeCompSupportMappings mor = do
  additions <- fmap concat (mapM witnessMappings (M.toList (mtClassifiedBy (dModes (morSrc mor)))))
  pure mor { morGenMap = M.union (morGenMap mor) (M.fromList additions) }
  where
    witnessMappings (modeSrc, classDecl) =
      case cdComp classDecl of
        Nothing -> Right []
        Just comp -> do
          maybePairs <- mapM (mkWitness modeSrc) [compCtxExt comp, compVar comp, compReindex comp]
          pure [pair | Just pair <- maybePairs]

    mkWitness modeSrc witnessName
      | M.member (modeSrc, witnessName) (morGenMap mor) = Right Nothing
      | otherwise =
          case M.lookup modeSrc (dGens (morSrc mor)) >>= M.lookup witnessName of
            Nothing -> Right Nothing
            Just srcGen -> do
              modeTgt <- PolyMor.applyMorphismMode mor modeSrc
              case M.lookup modeTgt (dGens (morTgt mor)) >>= M.lookup witnessName of
                Nothing -> Right Nothing
                Just _ -> do
                  img <- mappedIdentityGenImage mor srcGen
                  pure (Just ((modeSrc, witnessName), img))

computePolyPushout :: Text -> Morphism -> Morphism -> Either Text PolyPushoutResult
computePolyPushout name morL morR =
  let morL' = normalizeMorphism morL
      morR' = normalizeMorphism morR
   in do
        morL'' <- completeCompSupportMappings morL'
        morR'' <- completeCompSupportMappings morR'
        PolyPush.computePolyPushout name morL'' morR''

computePolyPushoutPreferRight :: Text -> Text -> Morphism -> Morphism -> Either Text PolyPushoutResult
computePolyPushoutPreferRight name tag morL morR =
  let morL' = normalizeMorphism morL
      morR' = normalizeMorphism morR
   in do
        morL'' <- completeCompSupportMappings morL'
        morR'' <- completeCompSupportMappings morR'
        PolyPush.computePolyPushoutPreferRight name tag morL'' morR''

computePolyCoproduct :: Text -> Doctrine -> Doctrine -> Either Text PolyPushoutResult
computePolyCoproduct name a b =
  PolyPush.computePolyCoproduct name (normalizeDoctrine a) (normalizeDoctrine b)

checkImplementsObligations env schema impl target =
  PolyElab.checkImplementsObligations env (normalizeDoctrine schema) (normalizeMorphism impl) (normalizeDoctrine target)

mkModes :: S.Set ModeName -> ModeTheory
mkModes modes =
  ModeTheory
    { mtModes = M.fromList [ (m, ModeInfo { miName = m, miDefEqEngine = DefEqTRS }) | m <- S.toList modes ]
    , mtDecls = M.empty
    , mtEqns = []
    , mtTransforms = M.empty
    , mtClassifiedBy = M.empty
    , mtClassifierLifts = M.empty
    }

universeName :: ModeName -> ObjName
universeName (ModeName n) = ObjName ("U_" <> n)

universeObj :: ModeName -> Obj
universeObj mode = mkCon (ObjRef mode (universeName mode)) []

defaultUniverseObj :: ModeName -> Obj
defaultUniverseObj mode = mkCon (ObjRef mode (ObjName "U")) []

selfClassifiedModes :: S.Set ModeName -> ModeTheory
selfClassifiedModes modes =
  let mt = mkModes modes
  in mt
       { mtClassifiedBy =
           M.fromList
             [ (mode, ClassificationDecl { cdClassifier = mode, cdUniverse = universeObj mode, cdComp = Just compDecl })
             | mode <- S.toList modes
             ]
       }

objNameText :: ObjName -> Text
objNameText (ObjName n) = n

ctorDecl :: Obj -> ModeName -> ObjName -> [TypeParamSig] -> GenDecl
ctorDecl universeTy mode ctorName sig =
  GenDecl
    { gdName = GenName (objNameText ctorName)
    , gdMode = mode
    , gdParams = params
    , gdDom = []
    , gdCod = [universeTy]
    , gdLiteralKind = Nothing
    }
  where
    tyPos =
      [ (pos, v)
      | (pos, TPS_Ty m) <- zip [0 :: Int ..] sig
      , let v =
              TmVar
                { tmvName = "a" <> T.pack (show pos)
                , tmvSort = universeObj m
                , tmvScope = 0
                , tmvOwnerMode = Just m
                }
      ]
    tmPos =
      [ (pos, v)
      | (pos, TPS_Tm sortTy) <- zip [0 :: Int ..] sig
      , let v =
              TmVar
                { tmvName = "x" <> T.pack (show pos)
                , tmvSort = sortTy
                , tmvScope = 0
                , tmvOwnerMode = Just mode
                }
      ]
    tyVars = map snd tyPos
    tmVars = map snd tmPos
    params =
      [ case ps of
          TPS_Ty _ -> GP_Ty (lookupByPos pos tyPos)
          TPS_Tm _ -> GP_Tm (lookupByPos pos tmPos)
      | (pos, ps) <- zip [0 :: Int ..] sig
      ]
    lookupByPos pos xs =
      case lookup pos xs of
        Just v -> v
        Nothing -> error "ctorDecl: missing parameter position"

addSelfClassifications :: [ModeName] -> ModeTheory -> ModeTheory
addSelfClassifications modes mt =
  mt
    { mtClassifiedBy =
        foldl
          (\acc mode ->
              M.insertWith
                (\_ old -> old)
                mode
                (ClassificationDecl { cdClassifier = mode, cdUniverse = defaultUniverseObj mode, cdComp = Just compDecl })
                acc
          )
          (mtClassifiedBy mt)
          modes
    }

insertCtorDecls
  :: ModeName
  -> Obj
  -> [(ObjName, [TypeParamSig])]
  -> M.Map ModeName (M.Map GenName GenDecl)
  -> M.Map ModeName (M.Map GenName GenDecl)
insertCtorDecls mode universeTy sigs gens0 =
  let ctorMap =
        M.fromList
          [ (gdName gd, gd)
          | (ctorName, sig) <- sigs
          , let gd = ctorDecl universeTy mode ctorName sig
          ]
      modeMap = M.findWithDefault M.empty mode gens0
   in M.insert mode (M.union modeMap ctorMap) gens0

withSelfClassifiedCtors :: [(ModeName, [(ObjName, [TypeParamSig])])] -> Doctrine -> Doctrine
withSelfClassifiedCtors entries doc =
  let modes' = addSelfClassifications (map fst entries) (dModes doc)
      universeFor mode =
        case M.lookup mode (mtClassifiedBy modes') of
          Just decl -> cdUniverse decl
          Nothing -> defaultUniverseObj mode
   in doc
        { dModes = modes'
        , dGens =
            foldl
              (\acc (mode, sigs) -> insertCompSupportGens mode (universeFor mode) (insertCtorDecls mode (universeFor mode) sigs acc))
              (dGens doc)
              entries
        }

compCtxExtName :: GenName
compCtxExtName = GenName "__ctx_ext"

compVarName :: GenName
compVarName = GenName "__var"

compReindexName :: GenName
compReindexName = GenName "__reindex"

compDecl :: CompDecl
compDecl =
  CompDecl
    { compCtxExt = compCtxExtName
    , compVar = compVarName
    , compReindex = compReindexName
    }

mkCompGen :: ModeName -> Obj -> GenName -> GenDecl
mkCompGen mode aTy name =
  GenDecl
    { gdName = name
    , gdMode = mode
    , gdParams = []
    , gdDom = [InPort aTy]
    , gdCod = [aTy]
    , gdLiteralKind = Nothing
    }

insertCompSupportGens
  :: ModeName
  -> Obj
  -> M.Map ModeName (M.Map GenName GenDecl)
  -> M.Map ModeName (M.Map GenName GenDecl)
insertCompSupportGens mode aTy gens0 =
  let modeGens = M.findWithDefault M.empty mode gens0
      support =
        [ mkCompGen mode aTy compCtxExtName
        , mkCompGen mode aTy compVarName
        , mkCompGen mode aTy compReindexName
        ]
      modeGens' = foldl (\acc gd -> M.insertWith (\_ old -> old) (gdName gd) gd acc) modeGens support
   in M.insert mode modeGens' gens0

attachComprehensionFixture :: ModeName -> Obj -> Doctrine -> Doctrine
attachComprehensionFixture mode aTy doc =
  let modeGens0 = M.findWithDefault M.empty mode (dGens doc)
      compGens =
        [ mkCompGen mode aTy compCtxExtName
        , mkCompGen mode aTy compVarName
        , mkCompGen mode aTy compReindexName
        ]
      modeGens1 = foldl (\acc gd -> M.insert (gdName gd) gd acc) modeGens0 compGens
      modes0 = dModes doc
      classDecl0 = M.findWithDefault defaultClassDecl mode (mtClassifiedBy modes0)
      classDecl1 =
        classDecl0
          { cdComp =
              Just
                CompDecl
                  { compCtxExt = compCtxExtName
                  , compVar = compVarName
                  , compReindex = compReindexName
                  }
          }
      modes1 = modes0 { mtClassifiedBy = M.insert mode classDecl1 (mtClassifiedBy modes0) }
   in doc { dModes = modes1, dGens = M.insert mode modeGens1 (dGens doc) }
  where
    defaultClassDecl =
      ClassificationDecl
        { cdClassifier = mode
        , cdUniverse = defaultUniverseObj mode
        
        , cdComp = Just compDecl
        }

compIdentityImages :: ModeName -> Obj -> Either Text [((ModeName, GenName), GenImage)]
compIdentityImages mode aTy = do
  ctxExtImg <- plainImage <$> genD mode [aTy] [aTy] compCtxExtName
  varImg <- plainImage <$> genD mode [aTy] [aTy] compVarName
  reindexImg <- plainImage <$> genD mode [aTy] [aTy] compReindexName
  pure
    [ ((mode, compCtxExtName), ctxExtImg)
    , ((mode, compVarName), varImg)
    , ((mode, compReindexName), reindexImg)
    ]


testPushoutDedupByBody :: Assertion
testPushoutDedupByBody = do
  let mode = ModeName "M"
  base <- case mkDoctrine mode "Interface" (tvar mode "a") "eqI" of
    Left err -> assertFailure err
    Right d -> pure d
  left <- case mkDoctrine mode "Left" (tvar mode "a") "eqLeft" of
    Left err -> assertFailure err
    Right d -> pure d
  right <- case mkDoctrine mode "Right" (tvar mode "b") "eqRight" of
    Left err -> assertFailure err
    Right d -> pure d
  let morLeft = mkInclusionMorph "Left.in" base left (tvar mode "a")
  let morRight = mkInclusionMorph "Right.in" base right (tvar mode "b")
  res <- case computePolyPushout "Po" morLeft morRight of
    Left err -> assertFailure (show err)
    Right r -> pure r
  length (dCells2 (poDoctrine res)) @?= 1


mkDoctrine :: ModeName -> Text -> TmVar -> Text -> Either String Doctrine
mkDoctrine mode name tyVar cellName = do
  let gen = GenDecl
        { gdName = GenName "f"
        , gdMode = mode
        , gdParams = [GP_Ty (tyVar)]
        , gdDom = map InPort [OVar tyVar]
        , gdCod = [OVar tyVar]
        , gdLiteralKind = Nothing
        }
  lhs <- case genericGenDiagram gen of
    Left err -> Left (show err)
    Right d -> Right d
  let rhs = idD mode [OVar tyVar]
  let cell = Cell2
        { c2Name = cellName
        , c2Class = Computational
        , c2Orient = LR
        , c2Params = map GP_Ty [tyVar] <> map GP_Tm []
        , c2LHS = lhs
        , c2RHS = rhs
        }
  let doc = Doctrine
        { dName = name
        , dModes = mkModes (S.singleton mode)
    , dAcyclicModes = S.empty
        , dGens = M.fromList [(mode, M.fromList [(gdName gen, gen)])]
        , dCells2 = [cell]
      , dActions = M.empty
      , dObligations = []
                }
  case validateDoctrine doc of
    Left err -> Left (show err)
    Right () -> Right doc

mkInclusionMorph :: Text -> Doctrine -> Doctrine -> TmVar -> Morphism
mkInclusionMorph name src tgt tyVar =
  let mode = ModeName "M"
      tgtGen =
        case M.lookup mode (dGens tgt) >>= M.lookup (GenName "f") of
          Nothing -> error "mkInclusionMorph: missing target generator"
          Just gd -> gd
      img =
        case identityGenImage tgtGen of
          Left _ -> error "mkInclusionMorph: identityGenImage failed"
          Right gi -> gi
      genMap = M.fromList [((mode, GenName "f"), img)]
  in Morphism
      { morName = name
      , morSrc = src
      , morTgt = tgt
      , morIsCoercion = False
      , morModeMap = identityModeMap src
      , morModMap = identityModMap src
      , morTypeMap = M.empty
      , morGenMap = genMap
        , morCheck = CheckAll
      , morPolicy = UseAllOriented
      }

testPushoutMergeOrient :: Assertion
testPushoutMergeOrient = do
  let mode = ModeName "M"
  base <- require (mkCellDoctrine mode "A" Structural LR)
  left <- require (mkCellDoctrine mode "B" Structural LR)
  right <- require (mkCellDoctrine mode "C" Structural RL)
  let morLeft = mkIdMorph "fLeft" base left
  let morRight = mkIdMorph "fRight" base right
  res <- require (computePolyPushout "P" morLeft morRight)
  cell <- requireCell (poDoctrine res) "eq"
  assertEqual "expected merged orientation to become bidirectional" Bidirectional (c2Orient cell)
  assertEqual "expected merged class to remain structural" Structural (c2Class cell)

testPushoutMergeClass :: Assertion
testPushoutMergeClass = do
  let mode = ModeName "M"
  base <- require (mkCellDoctrine mode "A" Computational LR)
  left <- require (mkCellDoctrine mode "B" Structural LR)
  right <- require (mkCellDoctrine mode "C" Computational LR)
  let morLeft = mkIdMorph "fLeft" base left
  let morRight = mkIdMorph "fRight" base right
  res <- require (computePolyPushout "P" morLeft morRight)
  cell <- requireCell (poDoctrine res) "eq"
  assertEqual "expected merged orientation to remain LR" LR (c2Orient cell)
  assertEqual "expected merged class to become structural" Structural (c2Class cell)

testPushoutNameConflict :: Assertion
testPushoutNameConflict = do
  let mode = ModeName "M"
  base <- require (mkCellDoctrine mode "A" Computational LR)
  left <- require (mkCellDoctrine mode "B" Computational LR)
  right <- require (mkCellDoctrineWithAlt mode "C" Computational LR)
  let morLeft = mkIdMorph "fLeft" base left
  let morRight = mkIdMorph "fRight" base right
  case computePolyPushout "P" morLeft morRight of
    Left _ -> pure ()
    Right _ -> assertFailure "expected name conflict error"

mkCellDoctrine :: ModeName -> Text -> RuleClass -> Orientation -> Either Text Doctrine
mkCellDoctrine mode name cls orient = do
  let genF = GenDecl
        { gdName = GenName "f"
        , gdMode = mode
        , gdParams = []
        , gdDom = map InPort [tcon mode "A" []]
        , gdCod = [tcon mode "A" []]
        , gdLiteralKind = Nothing
        }
  let genG = GenDecl
        { gdName = GenName "g"
        , gdMode = mode
        , gdParams = []
        , gdDom = map InPort [tcon mode "A" []]
        , gdCod = [tcon mode "A" []]
        , gdLiteralKind = Nothing
        }
  lhs <- genD mode [tcon mode "A" []] [tcon mode "A" []] (gdName genF)
  rhs <- genD mode [tcon mode "A" []] [tcon mode "A" []] (gdName genG)
  let cell = Cell2
        { c2Name = "eq"
        , c2Class = cls
        , c2Orient = orient
        , c2Params = []
        , c2LHS = lhs
        , c2RHS = rhs
        }
  let doc =
        withSelfClassifiedCtors
          [(mode, [(ObjName "A", [])])]
          Doctrine
            { dName = name
            , dModes = mkModes (S.singleton mode)
            , dAcyclicModes = S.empty
            , dGens = M.fromList [(mode, M.fromList [(gdName genF, genF), (gdName genG, genG)])]
            , dCells2 = [cell]
            , dActions = M.empty
            , dObligations = []
                        }
  case validateDoctrine doc of
    Left err -> Left err
    Right () -> Right doc

mkCellDoctrineWithAlt :: ModeName -> Text -> RuleClass -> Orientation -> Either Text Doctrine
mkCellDoctrineWithAlt mode name cls orient = do
  let genF = GenDecl
        { gdName = GenName "f"
        , gdMode = mode
        , gdParams = []
        , gdDom = map InPort [tcon mode "A" []]
        , gdCod = [tcon mode "A" []]
        , gdLiteralKind = Nothing
        }
  let genG = GenDecl
        { gdName = GenName "g"
        , gdMode = mode
        , gdParams = []
        , gdDom = map InPort [tcon mode "A" []]
        , gdCod = [tcon mode "A" []]
        , gdLiteralKind = Nothing
        }
  lhs <- genD mode [tcon mode "A" []] [tcon mode "A" []] (gdName genG)
  rhs <- genD mode [tcon mode "A" []] [tcon mode "A" []] (gdName genF)
  let cell = Cell2
        { c2Name = "eq"
        , c2Class = cls
        , c2Orient = orient
        , c2Params = []
        , c2LHS = lhs
        , c2RHS = rhs
        }
  let doc =
        withSelfClassifiedCtors
          [(mode, [(ObjName "A", [])])]
          Doctrine
            { dName = name
            , dModes = mkModes (S.singleton mode)
            , dAcyclicModes = S.empty
            , dGens = M.fromList [(mode, M.fromList [(gdName genF, genF), (gdName genG, genG)])]
            , dCells2 = [cell]
            , dActions = M.empty
            , dObligations = []
                        }
  case validateDoctrine doc of
    Left err -> Left err
    Right () -> Right doc

mkIdMorph :: Text -> Doctrine -> Doctrine -> Morphism
mkIdMorph name src tgt =
  let mode = ModeName "M"
      mkImage gName =
        case genD mode [tcon mode "A" []] [tcon mode "A" []] gName of
          Left _ -> error "mkIdMorph: genD failed"
          Right d -> plainImage d
      genMap =
        M.fromList
          [ ((mode, GenName "f"), mkImage (GenName "f"))
          , ((mode, GenName "g"), mkImage (GenName "g"))
          ]
  in Morphism
      { morName = name
      , morSrc = src
      , morTgt = tgt
      , morIsCoercion = False
      , morModeMap = identityModeMap src
      , morModMap = identityModMap src
      , morTypeMap = M.empty
      , morGenMap = genMap
        , morCheck = CheckAll
      , morPolicy = UseAllOriented
      }

testPushoutTypePermutationCommutes :: Assertion
testPushoutTypePermutationCommutes = do
  let mode = ModeName "M"
  let prod = ObjName "Prod"
  let pair = ObjName "Pair"
  let aVar = tvar mode "a"
  let bVar = tvar mode "b"
  base <- case mkTypeDoctrine mode "A" [(prod, 2)] of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  left <- case mkTypeDoctrine mode "B" [(pair, 2)] of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  right <- case mkTypeDoctrine mode "C" [(prod, 2)] of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  let tmplF = TypeTemplate [GP_Ty (aVar), GP_Ty (bVar)] (mkCon (ObjRef mode pair) [OAObj (OVar bVar), OAObj (OVar aVar)])
  let morF = Morphism
        { morName = "f"
        , morSrc = base
        , morTgt = left
        , morIsCoercion = False
        , morModeMap = identityModeMap base
        , morModMap = identityModMap base
        , morTypeMap = M.fromList [(ObjRef mode prod, tmplF)]
        , morGenMap = M.empty
        , morCheck = CheckAll
        , morPolicy = UseAllOriented
        }
  let morG = Morphism
        { morName = "g"
        , morSrc = base
        , morTgt = right
        , morIsCoercion = False
        , morModeMap = identityModeMap base
        , morModMap = identityModMap base
        , morTypeMap = M.empty
        , morGenMap = M.empty
        , morCheck = CheckAll
        , morPolicy = UseAllOriented
        }
  res <- case computePolyPushout "P" morF morG of
    Left err -> assertFailure (T.unpack err)
    Right r -> pure r
  let diagA = idD mode [mkCon (ObjRef mode prod) [OAObj (OVar aVar), OAObj (OVar bVar)]]
  d1 <- case applyMorphismDiagram morF diagA of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  d2 <- case applyMorphismDiagram (poInl res) d1 of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  d3 <- case applyMorphismDiagram (poGlue res) diagA of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  iso <- case diagramIsoEq d2 d3 of
    Left err -> assertFailure (T.unpack err)
    Right ok -> pure ok
  assertBool "expected pushout type permutation to commute" iso

testPushoutAcceptsModeMap :: Assertion
testPushoutAcceptsModeMap = do
  let modeM = ModeName "M"
  let modeN = ModeName "N"
  let modes = mkModes (S.fromList [modeM, modeN])
  let base = Doctrine
        { dName = "Base"
        , dModes = modes
    , dAcyclicModes = S.empty
        , dGens = M.empty
        , dCells2 = []
      , dActions = M.empty
      , dObligations = []
                }
  let left = base { dName = "Left" }
  let right = base { dName = "Right" }
  let modeMap = M.fromList [(modeM, modeN), (modeN, modeN)]
  let morF = Morphism
        { morName = "f"
        , morSrc = base
        , morTgt = left
        , morIsCoercion = False
        , morModeMap = modeMap
        , morModMap = identityModMap base
        , morTypeMap = M.empty
        , morGenMap = M.empty
        , morCheck = CheckAll
        , morPolicy = UseAllOriented
        }
  let morG = Morphism
        { morName = "g"
        , morSrc = base
        , morTgt = right
        , morIsCoercion = False
        , morModeMap = modeMap
        , morModMap = identityModMap base
        , morTypeMap = M.empty
        , morGenMap = M.empty
        , morCheck = CheckAll
        , morPolicy = UseAllOriented
        }
  res <- case computePolyPushout "P" morF morG of
    Left err -> assertFailure (T.unpack err) >> error "unreachable"
    Right out -> pure out
  case validateDoctrine (poDoctrine res) of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()

testPushoutTypeRefsStayInPushoutModes :: Assertion
testPushoutTypeRefsStayInPushoutModes = do
  let modeI = ModeName "I"
  let modeL = ModeName "L"
  let modeM = ModeName "M"
  let mkTypeDoc name mode =
        withSelfClassifiedCtors
          [(mode, [(ObjName "A", [])])]
          Doctrine
            { dName = name
            , dModes = mkModes (S.singleton mode)
            , dAcyclicModes = S.empty
            , dGens = M.empty
            , dCells2 = []
            , dActions = M.empty
            , dObligations = []
                        }
  let src = mkTypeDoc "SrcTypeMode" modeI
  let left = mkTypeDoc "LeftTypeMode" modeL
  let right = mkTypeDoc "RightTypeMode" modeM
  mapM_ (either (assertFailure . T.unpack) pure . validateDoctrine) [src, left, right]
  let morF =
        Morphism
          { morName = "fTypeMode"
          , morSrc = src
          , morTgt = left
          , morIsCoercion = False
          , morModeMap = M.singleton modeI modeL
          , morModMap = M.empty
          , morTypeMap = M.empty
          , morGenMap = M.empty
          , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  let morG =
        Morphism
          { morName = "gTypeMode"
          , morSrc = src
          , morTgt = right
          , morIsCoercion = False
          , morModeMap = M.singleton modeI modeM
          , morModMap = M.empty
          , morTypeMap = M.empty
          , morGenMap = M.empty
          , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  res <- case computePolyPushout "PTypeMode" morF morG of
    Left err -> assertFailure (T.unpack err) >> error "unreachable"
    Right out -> pure out
  case validateDoctrine (poDoctrine res) of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  ctorTables <- require (PolyDoc.deriveCtorTables (poDoctrine res))
  assertBool
    "expected no derived ctor table under source mode I"
    (M.notMember modeI ctorTables || M.null (M.findWithDefault M.empty modeI ctorTables))

testPushoutDisjointCellRenameUsesOriginalModeKey :: Assertion
testPushoutDisjointCellRenameUsesOriginalModeKey = do
  let modeI = ModeName "I"
  let modeL = ModeName "L"
  let modeM = ModeName "M"
  let tyL = tcon modeL "A" []
  let src =
        Doctrine
          { dName = "SrcCellModeMap"
          , dModes = mkModes (S.singleton modeI)
          , dAcyclicModes = S.empty
          , dGens = M.empty
          , dCells2 = []
          , dActions = M.empty
          , dObligations = []
                    }
  lhs <- require (genD modeL [tyL] [tyL] (GenName "f"))
  rhs <- require (genD modeL [tyL] [tyL] (GenName "g"))
  let leftCell =
        Cell2
          { c2Name = "eq"
          , c2Class = Computational
          , c2Orient = LR
          , c2Params = []
          , c2LHS = lhs
          , c2RHS = rhs
          }
  let left =
        withSelfClassifiedCtors
          [(modeL, [(ObjName "A", [])])]
          Doctrine
            { dName = "LeftCellModeMap"
            , dModes = mkModes (S.singleton modeL)
            , dAcyclicModes = S.empty
            , dGens =
                M.singleton
                  modeL
                  ( M.fromList
                      [ (GenName "f", GenDecl (GenName "f") modeL [] [InPort tyL] [tyL] Nothing)
                      , (GenName "g", GenDecl (GenName "g") modeL [] [InPort tyL] [tyL] Nothing)
                      ]
                  )
            , dCells2 = [leftCell]
            , dActions = M.empty
            , dObligations = []
                        }
  let right =
        Doctrine
          { dName = "RightCellModeMap"
          , dModes = mkModes (S.singleton modeM)
          , dAcyclicModes = S.empty
          , dGens = M.empty
          , dCells2 = []
          , dActions = M.empty
          , dObligations = []
                    }
  mapM_ (either (assertFailure . T.unpack) pure . validateDoctrine) [src, left, right]
  let morF =
        Morphism
          { morName = "fCellModeMap"
          , morSrc = src
          , morTgt = left
          , morIsCoercion = False
          , morModeMap = M.singleton modeI modeL
          , morModMap = M.empty
          , morTypeMap = M.empty
          , morGenMap = M.empty
          , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  let morG =
        Morphism
          { morName = "gCellModeMap"
          , morSrc = src
          , morTgt = right
          , morIsCoercion = False
          , morModeMap = M.singleton modeI modeM
          , morModMap = M.empty
          , morTypeMap = M.empty
          , morGenMap = M.empty
          , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  res <- case computePolyPushout "PCellModeMap" morF morG of
    Left err -> assertFailure (T.unpack err) >> error "unreachable"
    Right out -> pure out
  let names = map c2Name (dCells2 (poDoctrine res))
  assertBool "expected non-interface cell name to be renamed" ("eq" `notElem` names)
  let renamed = [ name | name <- names, "LeftCellModeMap_inl_eq" `T.isPrefixOf` name ]
  assertBool "expected prefixed left-cell name after mode renaming" (not (null renamed))

testPushoutDisjointRenamesAfterModeCollapse :: Assertion
testPushoutDisjointRenamesAfterModeCollapse = do
  let modeI1 = ModeName "I1"
  let modeI2 = ModeName "I2"
  let modeL1 = ModeName "L1"
  let modeL2 = ModeName "L2"
  let modeM = ModeName "M"
  let tyL1 = tcon modeL1 "B" []
  let tyL2 = tcon modeL2 "B" []
  lhsL1 <- require (genD modeL1 [tyL1] [tyL1] (GenName "f"))
  rhsL1 <- require (genD modeL1 [tyL1] [tyL1] (GenName "g"))
  lhsL2 <- require (genD modeL2 [tyL2] [tyL2] (GenName "f"))
  rhsL2 <- require (genD modeL2 [tyL2] [tyL2] (GenName "g"))
  let src =
        Doctrine
          { dName = "SrcCollapse"
          , dModes = mkModes (S.fromList [modeI1, modeI2])
          , dAcyclicModes = S.empty
          , dGens = M.empty
          , dCells2 = []
          , dActions = M.empty
          , dObligations = []
                    }
  let left =
        withSelfClassifiedCtors
          [ (modeL1, [(ObjName "B", [])])
          , (modeL2, [(ObjName "B", [])])
          ]
          Doctrine
            { dName = "LeftCollapse"
            , dModes = mkModes (S.fromList [modeL1, modeL2])
            , dAcyclicModes = S.empty
            , dGens =
                M.fromList
                  [ ( modeL1
                    , M.fromList
                        [ (GenName "f", GenDecl (GenName "f") modeL1 [] [InPort tyL1] [tyL1] Nothing)
                        , (GenName "g", GenDecl (GenName "g") modeL1 [] [InPort tyL1] [tyL1] Nothing)
                        ]
                    )
                  , ( modeL2
                    , M.fromList
                        [ (GenName "f", GenDecl (GenName "f") modeL2 [] [InPort tyL2] [tyL2] Nothing)
                        , (GenName "g", GenDecl (GenName "g") modeL2 [] [InPort tyL2] [tyL2] Nothing)
                        ]
                    )
                  ]
            , dCells2 =
                [ Cell2 { c2Name = "eq", c2Class = Computational, c2Orient = LR, c2Params = [], c2LHS = lhsL1, c2RHS = rhsL1 }
                , Cell2 { c2Name = "eq", c2Class = Computational, c2Orient = LR, c2Params = [], c2LHS = lhsL2, c2RHS = rhsL2 }
                ]
            , dActions = M.empty
            , dObligations = []
                        }
  let right =
        Doctrine
          { dName = "RightCollapse"
          , dModes = mkModes (S.singleton modeM)
          , dAcyclicModes = S.empty
          , dGens = M.empty
          , dCells2 = []
          , dActions = M.empty
          , dObligations = []
                    }
  mapM_ (either (assertFailure . T.unpack) pure . validateDoctrine) [src, left, right]
  let morF =
        Morphism
          { morName = "fCollapse"
          , morSrc = src
          , morTgt = left
          , morIsCoercion = False
          , morModeMap = M.fromList [(modeI1, modeL1), (modeI2, modeL2)]
          , morModMap = M.empty
          , morTypeMap = M.empty
          , morGenMap = M.empty
          , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  let morG =
        Morphism
          { morName = "gCollapse"
          , morSrc = src
          , morTgt = right
          , morIsCoercion = False
          , morModeMap = M.fromList [(modeI1, modeM), (modeI2, modeM)]
          , morModMap = M.empty
          , morTypeMap = M.empty
          , morGenMap = M.empty
          , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  case computePolyPushout "PCollapse" morF morG of
    Left err ->
      assertBool
        ("expected comprehension-witness mismatch under mode collapse, got: " <> T.unpack err)
        ("comprehension witness mismatch" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected strict pushout to reject mode collapse with divergent comprehension witnesses"

testPushoutCellNamesArePerMode :: Assertion
testPushoutCellNamesArePerMode = do
  let modeI1 = ModeName "I1"
  let modeI2 = ModeName "I2"
  let modeL = ModeName "L"
  let modeR = ModeName "R"
  let src =
        Doctrine
          { dName = "SrcPerMode"
          , dModes = mkModes (S.fromList [modeI1, modeI2])
          , dAcyclicModes = S.empty
          , dGens = M.empty
          , dCells2 = []
          , dActions = M.empty
          , dObligations = []
                    }
  let tyL = tcon modeL "A" []
  let tyR = tcon modeR "A" []
  lhsL <- require (genD modeL [tyL] [tyL] (GenName "f"))
  rhsL <- require (genD modeL [tyL] [tyL] (GenName "g"))
  lhsR <- require (genD modeR [tyR] [tyR] (GenName "f"))
  rhsR <- require (genD modeR [tyR] [tyR] (GenName "g"))
  let left =
        withSelfClassifiedCtors
          [ (modeL, [(ObjName "A", [])])
          , (modeR, [(ObjName "A", [])])
          ]
          Doctrine
            { dName = "LeftPerMode"
            , dModes = mkModes (S.fromList [modeL, modeR])
            , dAcyclicModes = S.empty
            , dGens =
                M.fromList
                  [ ( modeL
                    , M.fromList
                        [ (GenName "f", GenDecl (GenName "f") modeL [] [InPort tyL] [tyL] Nothing)
                        , (GenName "g", GenDecl (GenName "g") modeL [] [InPort tyL] [tyL] Nothing)
                        ]
                    )
                  , ( modeR
                    , M.fromList
                        [ (GenName "f", GenDecl (GenName "f") modeR [] [InPort tyR] [tyR] Nothing)
                        , (GenName "g", GenDecl (GenName "g") modeR [] [InPort tyR] [tyR] Nothing)
                        ]
                    )
                  ]
            , dCells2 =
                [ Cell2 { c2Name = "eq", c2Class = Computational, c2Orient = LR, c2Params = [], c2LHS = lhsL, c2RHS = rhsL }
                , Cell2 { c2Name = "eq", c2Class = Computational, c2Orient = LR, c2Params = [], c2LHS = lhsR, c2RHS = rhsR }
                ]
            , dActions = M.empty
            , dObligations = []
                        }
  let right =
        Doctrine
          { dName = "RightPerMode"
          , dModes = mkModes (S.fromList [modeL, modeR])
          , dAcyclicModes = S.empty
          , dGens = M.empty
          , dCells2 = []
          , dActions = M.empty
          , dObligations = []
                    }
  mapM_ (either (assertFailure . T.unpack) pure . validateDoctrine) [src, left, right]
  let morLeft =
        Morphism
          { morName = "fPerMode"
          , morSrc = src
          , morTgt = left
          , morIsCoercion = False
          , morModeMap = M.fromList [(modeI1, modeL), (modeI2, modeR)]
          , morModMap = M.empty
          , morTypeMap = M.empty
          , morGenMap = M.empty
          , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  let morRight =
        Morphism
          { morName = "gPerMode"
          , morSrc = src
          , morTgt = right
          , morIsCoercion = False
          , morModeMap = M.fromList [(modeI1, modeL), (modeI2, modeR)]
          , morModMap = M.empty
          , morTypeMap = M.empty
          , morGenMap = M.empty
          , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  res <- case computePolyPushout "PPerModeCells" morLeft morRight of
    Left err -> assertFailure (T.unpack err) >> error "unreachable"
    Right out -> pure out
  let cells = dCells2 (poDoctrine res)
  assertBool "expected both per-mode cells to survive merge" (length cells == 2)
  assertBool "expected same cell name to be allowed across modes" (S.size (S.fromList (map c2Name cells)) == 1)
  assertBool "expected one surviving cell per mode" (S.fromList (map (dMode . c2LHS) cells) == S.fromList [modeL, modeR])

testPushoutNonInjectiveTypeCompatible :: Assertion
testPushoutNonInjectiveTypeCompatible = do
  let mode = ModeName "M"
  let mkDoc name typeNames =
        withSelfClassifiedCtors
          [(mode, [ (ObjName n, []) | n <- typeNames ])]
          Doctrine
            { dName = name
            , dModes = mkModes (S.singleton mode)
            , dAcyclicModes = S.empty
            , dGens = M.empty
            , dCells2 = []
            , dActions = M.empty
            , dObligations = []
                        }
  let src = mkDoc "SrcNI" ["X", "Y"]
  let left = mkDoc "LeftNI" ["T"]
  let right = mkDoc "RightNI" ["U1", "V1"]
  mapM_ (either (assertFailure . T.unpack) pure . validateDoctrine) [src, left, right]
  let tmpl tgtName = TypeTemplate [] (mkCon (ObjRef mode (ObjName tgtName)) [])
  let morF =
        Morphism
          { morName = "fNI"
          , morSrc = src
          , morTgt = left
          , morIsCoercion = False
          , morModeMap = identityModeMap src
          , morModMap = identityModMap src
          , morTypeMap =
              M.fromList
                [ (ObjRef mode (ObjName "X"), tmpl "T")
                , (ObjRef mode (ObjName "Y"), tmpl "T")
                ]
          , morGenMap = M.empty
          , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  let morG =
        Morphism
          { morName = "gNI"
          , morSrc = src
          , morTgt = right
          , morIsCoercion = False
          , morModeMap = identityModeMap src
          , morModMap = identityModMap src
          , morTypeMap =
              M.fromList
                [ (ObjRef mode (ObjName "X"), tmpl "U1")
                , (ObjRef mode (ObjName "Y"), tmpl "V1")
                ]
          , morGenMap = M.empty
          , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  res <- case computePolyPushout "PNIType" morF morG of
    Left err -> assertFailure (T.unpack err) >> error "unreachable"
    Right out -> pure out
  ctorTables <- require (PolyDoc.deriveCtorTables (poDoctrine res))
  let ctorsAtM = M.findWithDefault M.empty mode ctorTables
  let nonUniverse = [ name | name <- M.keys ctorsAtM, name /= ObjName "U" ]
  length nonUniverse @?= 1

testPushoutNonInjectiveLiteralKindIncompatible :: Assertion
testPushoutNonInjectiveLiteralKindIncompatible = do
  let mode = ModeName "M"
  let mkDoc name ctorName litKind =
        setCtorLiteralKind ctorName litKind $
          withSelfClassifiedCtors
            [(mode, [(ObjName ctorName, [])])]
            Doctrine
              { dName = name
              , dModes = mkModes (S.singleton mode)
              , dAcyclicModes = S.empty
              , dGens = M.empty
              , dCells2 = []
              , dActions = M.empty
              , dObligations = []
              }
      tmpl tgtName = TypeTemplate [] (mkCon (ObjRef mode (ObjName tgtName)) [])
      setCtorLiteralKind ctorName litKind doc =
        doc
          { dGens =
              M.adjust
                (M.adjust (\gd -> gd { gdLiteralKind = litKind }) (GenName ctorName))
                mode
                (dGens doc)
          }
  let src = mkDoc "SrcLitNI" "S" Nothing
  let left = mkDoc "LeftLitNI" "T" (Just LKInt)
  let right = mkDoc "RightLitNI" "U" (Just LKBool)
  mapM_ (either (assertFailure . T.unpack) pure . validateDoctrine) [src, left, right]
  let morF =
        Morphism
          { morName = "fLitNI"
          , morSrc = src
          , morTgt = left
          , morIsCoercion = False
          , morModeMap = identityModeMap src
          , morModMap = identityModMap src
          , morTypeMap = M.singleton (ObjRef mode (ObjName "S")) (tmpl "T")
          , morGenMap = M.empty
          , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  let morG =
        Morphism
          { morName = "gLitNI"
          , morSrc = src
          , morTgt = right
          , morIsCoercion = False
          , morModeMap = identityModeMap src
          , morModMap = identityModMap src
          , morTypeMap = M.singleton (ObjRef mode (ObjName "S")) (tmpl "U")
          , morGenMap = M.empty
          , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  case computePolyPushout "PNILit" morF morG of
    Left err ->
      assertBool
        ("expected incompatible merged literal kind error, got: " <> T.unpack err)
        ("incompatible merged literal kind" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected incompatible non-injective literal-kind mappings to fail"

testPushoutNonInjectiveGenCompatible :: Assertion
testPushoutNonInjectiveGenCompatible = do
  let mode = ModeName "M"
  let mkNullary name =
        GenDecl
          { gdName = GenName name
          , gdMode = mode
          , gdParams = []
          , gdDom = []
          , gdCod = []
          , gdLiteralKind = Nothing
          }
  let mkDoc name genNames =
        Doctrine
          { dName = name
          , dModes = mkModes (S.singleton mode)
          , dAcyclicModes = S.empty
          , dGens = M.singleton mode (M.fromList [ (GenName g, mkNullary g) | g <- genNames ])
          , dCells2 = []
          , dActions = M.empty
          , dObligations = []
                    }
  let src = mkDoc "SrcGenNI" ["g1", "g2"]
  let left = mkDoc "LeftGenNI" ["h"]
  let right = mkDoc "RightGenNI" ["u", "v"]
  mapM_ (either (assertFailure . T.unpack) pure . validateDoctrine) [src, left, right]
  imgH <- require (genD mode [] [] (GenName "h"))
  imgU <- require (genD mode [] [] (GenName "u"))
  imgV <- require (genD mode [] [] (GenName "v"))
  let morF =
        Morphism
          { morName = "fGenNI"
          , morSrc = src
          , morTgt = left
          , morIsCoercion = False
          , morModeMap = identityModeMap src
          , morModMap = identityModMap src
          , morTypeMap = M.empty
          , morGenMap =
              M.fromList
                [ ((mode, GenName "g1"), plainImage imgH)
                , ((mode, GenName "g2"), plainImage imgH)
                ]
          , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  let morG =
        Morphism
          { morName = "gGenNI"
          , morSrc = src
          , morTgt = right
          , morIsCoercion = False
          , morModeMap = identityModeMap src
          , morModMap = identityModMap src
          , morTypeMap = M.empty
          , morGenMap =
              M.fromList
                [ ((mode, GenName "g1"), plainImage imgU)
                , ((mode, GenName "g2"), plainImage imgV)
                ]
          , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  res <- case computePolyPushout "PNIGen" morF morG of
    Left err -> assertFailure (T.unpack err) >> error "unreachable"
    Right out -> pure out
  let gensAtM = M.findWithDefault M.empty mode (dGens (poDoctrine res))
  M.size gensAtM @?= 1

testPushoutNonInjectiveGenIncompatible :: Assertion
testPushoutNonInjectiveGenIncompatible = do
  let mode = ModeName "M"
  let aTy = tcon mode "A" []
  let gen1 =
        GenDecl
          { gdName = GenName "g1"
          , gdMode = mode
          , gdParams = []
          , gdDom = []
          , gdCod = []
          , gdLiteralKind = Nothing
          }
  let gen2 =
        GenDecl
          { gdName = GenName "g2"
          , gdMode = mode
          , gdParams = []
          , gdDom = [InPort aTy]
          , gdCod = []
          , gdLiteralKind = Nothing
          }
  let mkNullary name =
        GenDecl
          { gdName = GenName name
          , gdMode = mode
          , gdParams = []
          , gdDom = []
          , gdCod = []
          , gdLiteralKind = Nothing
          }
  let src =
        withSelfClassifiedCtors
          [(mode, [(ObjName "A", [])])]
          Doctrine
            { dName = "SrcGenBadNI"
            , dModes = mkModes (S.singleton mode)
            , dAcyclicModes = S.empty
            , dGens = M.singleton mode (M.fromList [(GenName "g1", gen1), (GenName "g2", gen2)])
            , dCells2 = []
            , dActions = M.empty
            , dObligations = []
                        }
  let left =
        withSelfClassifiedCtors
          [(mode, [(ObjName "A", [])])]
          Doctrine
            { dName = "LeftGenBadNI"
            , dModes = mkModes (S.singleton mode)
            , dAcyclicModes = S.empty
            , dGens = M.singleton mode (M.singleton (GenName "h") (mkNullary "h"))
            , dCells2 = []
            , dActions = M.empty
            , dObligations = []
                        }
  let right =
        withSelfClassifiedCtors
          [(mode, [(ObjName "A", [])])]
          Doctrine
            { dName = "RightGenBadNI"
            , dModes = mkModes (S.singleton mode)
            , dAcyclicModes = S.empty
            , dGens =
                M.singleton
                  mode
                  ( M.fromList
                      [ (GenName "u", mkNullary "u")
                      , (GenName "v", mkNullary "v")
                      ]
                  )
            , dCells2 = []
            , dActions = M.empty
            , dObligations = []
                        }
  mapM_ (either (assertFailure . T.unpack) pure . validateDoctrine) [src, left, right]
  imgH <- require (genD mode [] [] (GenName "h"))
  imgU <- require (genD mode [] [] (GenName "u"))
  imgV <- require (genD mode [] [] (GenName "v"))
  let morF =
        Morphism
          { morName = "fGenBadNI"
          , morSrc = src
          , morTgt = left
          , morIsCoercion = False
          , morModeMap = identityModeMap src
          , morModMap = identityModMap src
          , morTypeMap = M.empty
          , morGenMap =
              M.fromList
                [ ((mode, GenName "g1"), plainImage imgH)
                , ((mode, GenName "g2"), plainImage imgH)
                ]
          , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  let morG =
        Morphism
          { morName = "gGenBadNI"
          , morSrc = src
          , morTgt = right
          , morIsCoercion = False
          , morModeMap = identityModeMap src
          , morModMap = identityModMap src
          , morTypeMap = M.empty
          , morGenMap =
              M.fromList
                [ ((mode, GenName "g1"), plainImage imgU)
                , ((mode, GenName "g2"), plainImage imgV)
                ]
          , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  case computePolyPushout "PNIGenBad" morF morG of
    Left err ->
      assertBool
        ("expected incompatible merged generators error, got: " <> T.unpack err)
        ("incompatible merged generator signatures" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected incompatible non-injective generator mappings to fail"

testPushoutGlueComposesThroughInr :: Assertion
testPushoutGlueComposesThroughInr = do
  let mode = ModeName "M"
  let xTy = tcon mode "X" []
  let yTy = tcon mode "Y" []
  let genF =
        GenDecl
          { gdName = GenName "f"
          , gdMode = mode
          , gdParams = []
          , gdDom = [InPort xTy]
          , gdCod = [xTy]
          , gdLiteralKind = Nothing
          }
  let genH =
        GenDecl
          { gdName = GenName "h"
          , gdMode = mode
          , gdParams = []
          , gdDom = [InPort yTy]
          , gdCod = [yTy]
          , gdLiteralKind = Nothing
          }
  let src =
        withSelfClassifiedCtors
          [(mode, [(ObjName "X", [])])]
          Doctrine
            { dName = "SrcGlueCompose"
            , dModes = mkModes (S.singleton mode)
            , dAcyclicModes = S.empty
            , dGens = M.singleton mode (M.singleton (GenName "f") genF)
            , dCells2 = []
            , dActions = M.empty
            , dObligations = []
                        }
  let left = src { dName = "LeftGlueCompose" }
  let right =
        withSelfClassifiedCtors
          [(mode, [(ObjName "Y", [])])]
          Doctrine
            { dName = "RightGlueCompose"
            , dModes = mkModes (S.singleton mode)
            , dAcyclicModes = S.empty
            , dGens = M.singleton mode (M.singleton (GenName "h") genH)
            , dCells2 = []
            , dActions = M.empty
            , dObligations = []
                        }
  mapM_ (either (assertFailure . T.unpack) pure . validateDoctrine) [src, left, right]
  imgF <- require (genD mode [xTy] [xTy] (GenName "f"))
  imgH <- require (genD mode [yTy] [yTy] (GenName "h"))
  let inl =
        Morphism
          { morName = "inlGlueCompose"
          , morSrc = src
          , morTgt = left
          , morIsCoercion = False
          , morModeMap = identityModeMap src
          , morModMap = identityModMap src
          , morTypeMap = M.empty
          , morGenMap = M.singleton (mode, GenName "f") (plainImage imgF)
          , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  let rightType = TypeTemplate [] (mkCon (ObjRef mode (ObjName "Y")) [])
  let inrLeg =
        Morphism
          { morName = "inrGlueCompose"
          , morSrc = src
          , morTgt = right
          , morIsCoercion = False
          , morModeMap = identityModeMap src
          , morModMap = identityModMap src
          , morTypeMap = M.singleton (ObjRef mode (ObjName "X")) rightType
          , morGenMap = M.singleton (mode, GenName "f") (plainImage imgH)
          , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  res <- case computePolyPushout "PGlueCompose" inl inrLeg of
    Left err -> assertFailure (T.unpack err) >> error "unreachable"
    Right out -> pure out
  diagSrc <- require (genD mode [xTy] [xTy] (GenName "f"))
  diagTgt <- case applyMorphismDiagram (poGlue res) diagSrc of
    Left err -> assertFailure ("expected composed glue to elaborate through inr: " <> T.unpack err) >> error "unreachable"
    Right d -> pure d
  case IM.elems (dEdges diagTgt) of
    [edge] ->
      case ePayload edge of
        PGen gName _ _ -> gName @?= GenName "f"
        _ -> assertFailure "expected generator payload after glue composition"
    _ -> assertFailure "expected a single edge after glue composition"

testPushoutGenInjectiveByMode :: Assertion
testPushoutGenInjectiveByMode = do
  let modeL = ModeName "L"
  let modeR = ModeName "R"
  let modes = mkModes (S.fromList [modeL, modeR])
  let mkNullaryGen mode name =
        GenDecl
          { gdName = GenName name
          , gdMode = mode
          , gdParams = []
          , gdDom = []
          , gdCod = []
          , gdLiteralKind = Nothing
          }
  let mkDoc name genName =
        Doctrine
          { dName = name
          , dModes = modes
          , dAcyclicModes = S.empty
          , dGens =
              M.fromList
                [ (modeL, M.singleton (GenName genName) (mkNullaryGen modeL genName))
                , (modeR, M.singleton (GenName genName) (mkNullaryGen modeR genName))
                ]
          , dCells2 = []
          , dActions = M.empty
          , dObligations = []
                    }
  let src = mkDoc "SrcByMode" "g"
  let left = mkDoc "LeftByMode" "h"
  let right = mkDoc "RightByMode" "k"
  mapM_ (either (assertFailure . T.unpack) pure . validateDoctrine) [src, left, right]
  imgHL <- require (genD modeL [] [] (GenName "h"))
  imgHR <- require (genD modeR [] [] (GenName "h"))
  imgKL <- require (genD modeL [] [] (GenName "k"))
  imgKR <- require (genD modeR [] [] (GenName "k"))
  let morF =
        Morphism
          { morName = "fByMode"
          , morSrc = src
          , morTgt = left
          , morIsCoercion = False
          , morModeMap = identityModeMap src
          , morModMap = identityModMap src
          , morTypeMap = M.empty
          , morGenMap =
              M.fromList
                [ ((modeL, GenName "g"), plainImage imgHL)
                , ((modeR, GenName "g"), plainImage imgHR)
                ]
          , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  let morG =
        Morphism
          { morName = "gByMode"
          , morSrc = src
          , morTgt = right
          , morIsCoercion = False
          , morModeMap = identityModeMap src
          , morModMap = identityModMap src
          , morTypeMap = M.empty
          , morGenMap =
              M.fromList
                [ ((modeL, GenName "g"), plainImage imgKL)
                , ((modeR, GenName "g"), plainImage imgKR)
                ]
          , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  case computePolyPushout "PGenByMode" morF morG of
    Left err -> assertFailure (T.unpack err)
    Right _ -> pure ()

testPushoutTypeRenameDefaultUsesModeMap :: Assertion
testPushoutTypeRenameDefaultUsesModeMap = do
  let modeM = ModeName "M"
  let modeN = ModeName "N"
  let mkDoc name modeForType =
        withSelfClassifiedCtors
          [(modeForType, [(ObjName "X", [])])]
          Doctrine
            { dName = name
            , dModes = mkModes (S.singleton modeForType)
            , dAcyclicModes = S.empty
            , dGens = M.empty
            , dCells2 = []
            , dActions = M.empty
            , dObligations = []
                        }
  let src = mkDoc "SrcTypeRename" modeM
  let body = mkDoc "BodyTypeRename" modeN
  let target = mkDoc "TargetTypeRename" modeN
  mapM_ (either (assertFailure . T.unpack) pure . validateDoctrine) [src, body, target]
  let modeMap = M.singleton modeM modeN
  let incl =
        Morphism
          { morName = "inclTypeRename"
          , morSrc = src
          , morTgt = body
          , morIsCoercion = False
          , morModeMap = modeMap
          , morModMap = M.empty
          , morTypeMap = M.empty
          , morGenMap = M.empty
          , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  let impl =
        Morphism
          { morName = "implTypeRename"
          , morSrc = src
          , morTgt = target
          , morIsCoercion = False
          , morModeMap = modeMap
          , morModMap = M.empty
          , morTypeMap = M.empty
          , morGenMap = M.empty
          , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  res <- case computePolyPushoutPreferRight "PTypeRenameDefault" "TypeRename" incl impl of
    Left err -> assertFailure (T.unpack err) >> error "unreachable"
    Right out -> pure out
  ctorTables <- require (PolyDoc.deriveCtorTables (poDoctrine res))
  let ctorsAtN = M.findWithDefault M.empty modeN ctorTables
  assertBool "expected type X at mapped target mode N" (M.member (ObjName "X") ctorsAtN)

testPushoutClassificationUniverseFollowsTypeRename :: Assertion
testPushoutClassificationUniverseFollowsTypeRename = do
  let mode = ModeName "M"
  let typeName = ObjName "U"
  let universe = mkCon (ObjRef mode typeName) []
  let uGen =
        GenDecl
          { gdName = GenName "U"
          , gdMode = mode
          , gdParams = []
          , gdDom = []
          , gdCod = [universe]
          , gdLiteralKind = Nothing
          }
  let classDecl =
        ClassificationDecl
          { cdClassifier = mode
          , cdUniverse = universe
          
          , cdComp = Just compDecl
          }
  let src =
        withSelfClassifiedCtors
          [(mode, [(typeName, [])])]
          Doctrine
            { dName = "SrcClassRename"
            , dModes =
                (mkModes (S.singleton mode))
                  { mtClassifiedBy = M.singleton mode classDecl
                  }
            , dAcyclicModes = S.empty
            , dGens = M.singleton mode (M.singleton (gdName uGen) uGen)
            , dCells2 = []
            , dActions = M.empty
            , dObligations = []
                        }
  let left =
        withSelfClassifiedCtors
          [(mode, [(typeName, [])])]
          Doctrine
            { dName = "LeftClassRename"
            , dModes =
                (mkModes (S.singleton mode))
                  { mtClassifiedBy = M.singleton mode classDecl
                  }
            , dAcyclicModes = S.empty
            , dGens = M.singleton mode (M.singleton (gdName uGen) uGen)
            , dCells2 = []
            , dActions = M.empty
            , dObligations = []
                        }
  let right =
        withSelfClassifiedCtors
          [(mode, [(typeName, [])])]
          Doctrine
            { dName = "RightClassRename"
            , dModes = mkModes (S.singleton mode)
            , dAcyclicModes = S.empty
            , dGens = M.singleton mode (M.singleton (gdName uGen) uGen)
            , dCells2 = []
            , dActions = M.empty
            , dObligations = []
                        }
  mapM_ (either (assertFailure . T.unpack) pure . validateDoctrine) [src, left, right]
  let inl =
        Morphism
          { morName = "classInl"
          , morSrc = src
          , morTgt = left
          , morIsCoercion = False
          , morModeMap = identityModeMap src
          , morModMap = identityModMap src
          , morTypeMap = M.empty
          , morGenMap = M.empty
          , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  let inr =
        Morphism
          { morName = "classInr"
          , morSrc = src
          , morTgt = right
          , morIsCoercion = False
          , morModeMap = identityModeMap src
          , morModMap = identityModMap src
          , morTypeMap = M.empty
          , morGenMap = M.empty
          , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  res <- case computePolyPushout "PClassRename" inl inr of
    Left err -> assertFailure (T.unpack err) >> error "unreachable"
    Right out -> pure out
  decl <-
    case M.lookup mode (mtClassifiedBy (dModes (poDoctrine res))) of
      Nothing ->
        assertFailure "expected classifiedBy declaration in pushout doctrine" >> error "unreachable"
      Just out -> pure out
  expectedUniverse <- require (applyMorphismTy (poInl res) universe)
  cdUniverse decl @?= expectedUniverse

testPushoutAlphaRenameWithModeEq :: Assertion
testPushoutAlphaRenameWithModeEq = do
  let mode = ModeName "M"
  let modF = ModName "F"
  let modU = ModName "U"
  let mt = mkModeEqTheory mode modF modU
  base <- require (mkModeEqDoctrine "Base" mt "a" True)
  left <- require (mkModeEqDoctrine "Left" mt "x" False)
  right <- require (mkModeEqDoctrine "Right" mt "y" False)
  let morLeft = mkModeEqMorph "f" base left "x"
  let morRight = mkModeEqMorph "g" base right "y"
  res <- case computePolyPushout "P" morLeft morRight of
    Left err -> assertFailure (T.unpack err)
    Right out -> pure out
  case validateDoctrine (poDoctrine res) of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  let etaCells = [ cell | cell <- dCells2 (poDoctrine res), c2Name cell == "eta" ]
  length etaCells @?= 1
  case M.lookup mode (dGens (poDoctrine res)) >>= M.lookup (GenName "modal") of
    Nothing -> assertFailure "expected modal generator in pushout result"
    Just modalGen ->
      case gdPlainDom modalGen of
        [OMod me (OVar _)] -> mePath me @?= [modF]
        _ -> assertFailure "expected modal generator domain to retain non-canceling modality"

testPushoutTermTypeMaps :: Assertion
testPushoutTermTypeMaps = do
  let modeM = ModeName "M"
  let modeI = ModeName "I"
  let modeSet = S.fromList [modeM, modeI]
  let universeM = universeObj modeM
  let universeI = universeObj modeI
  let natRef = ObjRef modeI (ObjName "Nat")
  let vecRef = ObjRef modeM (ObjName "Vec")
  let vec2Ref = ObjRef modeM (ObjName "Vec2")
  let natTy = mkCon natRef []
  let genNat =
        GenDecl
          { gdName = GenName "Nat"
          , gdMode = modeI
          , gdParams = []
          , gdDom = []
          , gdCod = [universeI]
          , gdLiteralKind = Nothing
          }
  let vecTyVar =
        TmVar
          { tmvName = "a"
          , tmvSort = universeM
          , tmvScope = 1
          , tmvOwnerMode = Just modeM
          }
  let vecTmVar =
        TmVar
          { tmvName = "n"
          , tmvSort = natTy
          , tmvScope = -1
          , tmvOwnerMode = Just modeM
          }
  let genVec =
        GenDecl
          { gdName = GenName "Vec"
          , gdMode = modeM
          , gdParams = [GP_Tm vecTmVar, GP_Ty vecTyVar]
          , gdDom = []
          , gdCod = [universeM]
          , gdLiteralKind = Nothing
          }
  let vec2TyVar =
        TmVar
          { tmvName = "a"
          , tmvSort = universeM
          , tmvScope = 1
          , tmvOwnerMode = Just modeM
          }
  let vec2TmVar =
        TmVar
          { tmvName = "n"
          , tmvSort = natTy
          , tmvScope = -1
          , tmvOwnerMode = Just modeM
          }
  let genVec2 =
        GenDecl
          { gdName = GenName "Vec2"
          , gdMode = modeM
          , gdParams = [GP_Tm vec2TmVar, GP_Ty vec2TyVar]
          , gdDom = []
          , gdCod = [universeM]
          , gdLiteralKind = Nothing
          }
  let src =
        Doctrine
          { dName = "SrcIdx"
          , dModes = selfClassifiedModes modeSet
    , dAcyclicModes = S.empty
          , dGens =
              insertCompSupportGens modeI universeI $
                insertCompSupportGens modeM universeM $
                  M.fromList
                    [ (modeI, M.fromList [(gdName genNat, genNat)])
                    , (modeM, M.fromList [(gdName genVec, genVec)])
                    ]
          , dCells2 = []
      , dActions = M.empty
      , dObligations = []
                    }
  let left =
        Doctrine
          { dName = "LeftIdx"
          , dModes = selfClassifiedModes modeSet
    , dAcyclicModes = S.empty
          , dGens =
              insertCompSupportGens modeI universeI $
                insertCompSupportGens modeM universeM $
                  M.fromList
                    [ (modeI, M.fromList [(gdName genNat, genNat)])
                    , (modeM, M.fromList [(gdName genVec2, genVec2)])
                    ]
          , dCells2 = []
      , dActions = M.empty
      , dObligations = []
                    }
  let right = src { dName = "RightIdx" }
  case validateDoctrine src of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  case validateDoctrine left of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  case validateDoctrine right of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  let nVar = TmVar { tmvName = "n", tmvSort = natTy, tmvScope = 0, tmvOwnerMode = Nothing }
  let aVar = mkModeMetaVar "a" modeM
  let morF =
        Morphism
          { morName = "fIdx"
          , morSrc = src
          , morTgt = left
          , morIsCoercion = False
          , morModeMap = identityModeMap src
          , morModMap = identityModMap src
          , morTypeMap =
              M.fromList
                [ ( vecRef
                  , TypeTemplate
                      [GP_Tm nVar, GP_Ty (aVar)]
                      (mkCon vec2Ref [OATm (tmMeta nVar), OAObj (OVar aVar)])
                  )
                ]
          , morGenMap = M.empty
        , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  let morG =
        Morphism
          { morName = "gIdx"
          , morSrc = src
          , morTgt = right
          , morIsCoercion = False
          , morModeMap = identityModeMap src
          , morModMap = identityModMap src
          , morTypeMap = M.empty
          , morGenMap = M.empty
        , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  case computePolyPushout "PIdx" morF morG of
    Left err -> assertFailure (T.unpack err)
    Right _ -> pure ()

testPushoutTypePermutationSortRename :: Assertion
testPushoutTypePermutationSortRename = do
  let modeM = ModeName "M"
  let modeI = ModeName "I"
  let modeSet = S.fromList [modeM, modeI]
  let universeM = universeObj modeM
  let universeI = universeObj modeI
  let natRef = ObjRef modeI (ObjName "Nat")
  let natLRef = ObjRef modeI (ObjName "NatL")
  let vecRef = ObjRef modeM (ObjName "Vec")
  let vec2Ref = ObjRef modeM (ObjName "Vec2")
  let natTy = mkCon natRef []
  let natLTy = mkCon natLRef []
  let genNat =
        GenDecl
          { gdName = GenName "Nat"
          , gdMode = modeI
          , gdParams = []
          , gdDom = []
          , gdCod = [universeI]
          , gdLiteralKind = Nothing
          }
  let genNatL =
        GenDecl
          { gdName = GenName "NatL"
          , gdMode = modeI
          , gdParams = []
          , gdDom = []
          , gdCod = [universeI]
          , gdLiteralKind = Nothing
          }
  let vecTyVar =
        TmVar
          { tmvName = "a"
          , tmvSort = universeM
          , tmvScope = 1
          , tmvOwnerMode = Just modeM
          }
  let vecTmVar =
        TmVar
          { tmvName = "n"
          , tmvSort = natTy
          , tmvScope = -1
          , tmvOwnerMode = Just modeM
          }
  let genVec =
        GenDecl
          { gdName = GenName "Vec"
          , gdMode = modeM
          , gdParams = [GP_Tm vecTmVar, GP_Ty vecTyVar]
          , gdDom = []
          , gdCod = [universeM]
          , gdLiteralKind = Nothing
          }
  let vec2TyVar =
        TmVar
          { tmvName = "a"
          , tmvSort = universeM
          , tmvScope = 0
          , tmvOwnerMode = Just modeM
          }
  let vec2TmVar =
        TmVar
          { tmvName = "n"
          , tmvSort = natLTy
          , tmvScope = -2
          , tmvOwnerMode = Just modeM
          }
  let genVec2 =
        GenDecl
          { gdName = GenName "Vec2"
          , gdMode = modeM
          , gdParams = [GP_Ty vec2TyVar, GP_Tm vec2TmVar]
          , gdDom = []
          , gdCod = [universeM]
          , gdLiteralKind = Nothing
          }
  let src =
        Doctrine
          { dName = "SrcIdxSwap"
          , dModes = selfClassifiedModes modeSet
          , dAcyclicModes = S.empty
          , dGens =
              insertCompSupportGens modeI universeI $
                insertCompSupportGens modeM universeM $
                  M.fromList
                    [ (modeI, M.fromList [(gdName genNat, genNat)])
                    , (modeM, M.fromList [(gdName genVec, genVec)])
                    ]
          , dCells2 = []
          , dActions = M.empty
          , dObligations = []
                    }
  let left =
        Doctrine
          { dName = "LeftIdxSwap"
          , dModes = selfClassifiedModes modeSet
          , dAcyclicModes = S.empty
          , dGens =
              insertCompSupportGens modeI universeI $
                insertCompSupportGens modeM universeM $
                  M.fromList
                    [ (modeI, M.fromList [(gdName genNatL, genNatL)])
                    , (modeM, M.fromList [(gdName genVec2, genVec2)])
                    ]
          , dCells2 = []
          , dActions = M.empty
          , dObligations = []
                    }
  let right = src { dName = "RightIdxSwap" }
  case validateDoctrine src of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  case validateDoctrine left of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  case validateDoctrine right of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  let nVar = TmVar { tmvName = "n", tmvSort = natLTy, tmvScope = 0, tmvOwnerMode = Nothing }
  let aVar = mkModeMetaVar "a" modeM
  let morF =
        Morphism
          { morName = "fIdxSwap"
          , morSrc = src
          , morTgt = left
          , morIsCoercion = False
          , morModeMap = identityModeMap src
          , morModMap = identityModMap src
          , morTypeMap =
              M.fromList
                [ (natRef, TypeTemplate [] natLTy)
                , ( vecRef
                  , TypeTemplate
                      [GP_Tm nVar, GP_Ty (aVar)]
                      (mkCon vec2Ref [OAObj (OVar aVar), OATm (tmMeta nVar)])
                  )
                ]
          , morGenMap = M.empty
          , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  let morG =
        Morphism
          { morName = "gIdxSwap"
          , morSrc = src
          , morTgt = right
          , morIsCoercion = False
          , morModeMap = identityModeMap src
          , morModMap = identityModMap src
          , morTypeMap = M.empty
          , morGenMap = M.empty
          , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  res <- case computePolyPushout "PIdxSwap" morF morG of
    Left err -> assertFailure (T.unpack err)
    Right out -> pure out
  ctorTables <- require (PolyDoc.deriveCtorTables (poDoctrine res))
  let modeCtors = M.findWithDefault M.empty modeM ctorTables
  let expectedSig = [TPS_Tm natTy, TPS_Ty modeM]
  assertBool
    "expected merged Vec-type constructor signature in pushout result"
    (expectedSig `elem` M.elems modeCtors)

testCoproductMergesDistinctModeTheories :: Assertion
testCoproductMergesDistinctModeTheories = do
  let modeM = ModeName "M"
  let modeN = ModeName "N"
  let docA =
        withSelfClassifiedCtors
          [(modeM, [(ObjName "A", [])])]
          Doctrine
            { dName = "CopA"
            , dModes = mkModes (S.singleton modeM)
            , dAcyclicModes = S.empty
            , dGens = M.empty
            , dCells2 = []
            , dActions = M.empty
            , dObligations = []
                        }
  let docB =
        withSelfClassifiedCtors
          [(modeN, [(ObjName "B", [])])]
          Doctrine
            { dName = "CopB"
            , dModes = mkModes (S.singleton modeN)
            , dAcyclicModes = S.empty
            , dGens = M.empty
            , dCells2 = []
            , dActions = M.empty
            , dObligations = []
                        }
  case validateDoctrine docA of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  case validateDoctrine docB of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  res <- case computePolyCoproduct "PCopDistinct" docA docB of
    Left err -> assertFailure (T.unpack err)
    Right out -> pure out
  let outDoc = poDoctrine res
  assertBool "expected left mode in coproduct result" (M.member modeM (mtModes (dModes outDoc)))
  assertBool "expected right mode in coproduct result" (M.member modeN (mtModes (dModes outDoc)))

testCoproductObligationRenameElaborates :: Assertion
testCoproductObligationRenameElaborates = do
  let mode = ModeName "M"
  let natRef = ObjRef mode (ObjName "Nat")
  let natTy = mkCon natRef []
  let rawExpr = PolyAST.ROEDiag (PolyAST.RDId [PolyAST.RPTVar "Nat"])
  let obl =
        ObligationDecl
          { obName = "nat_refl"
          , obMode = mode
          , obForGen = False
          , obForGenName = Nothing
          , obGenerated = False
          , obParams = []
          , obDom = [natTy]
          , obCod = [natTy]
          , obLHSExpr = rawExpr
          , obRHSExpr = rawExpr
          , obPolicy = UseAllOriented
          }
  let docA =
        withSelfClassifiedCtors
          [(mode, [(ObjName "Nat", [])])]
          Doctrine
            { dName = "DocA"
            , dModes = mkModes (S.singleton mode)
            , dAcyclicModes = S.empty
            , dGens = M.empty
            , dCells2 = []
            , dActions = M.empty
            , dObligations = [obl]
                        }
  let docB =
        Doctrine
          { dName = "DocB"
          , dModes = mkModes (S.singleton mode)
          , dAcyclicModes = S.empty
          , dGens = M.empty
          , dCells2 = []
          , dActions = M.empty
          , dObligations = []
                    }
  case validateDoctrine docA of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  case validateDoctrine docB of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  out <- case computePolyCoproduct "POblRen" docA docB of
    Left err -> assertFailure (T.unpack err)
    Right res -> pure (poDoctrine res)
  let idMorph =
        Morphism
          { morName = "POblRen.id"
          , morSrc = out
          , morTgt = out
          , morIsCoercion = True
          , morModeMap = identityModeMap out
          , morModMap = identityModMap out
          , morTypeMap = M.empty
          , morGenMap = M.empty
          , morCheck = CheckNone
          , morPolicy = UseAllOriented
          }
  case checkImplementsObligations emptyEnv out idMorph out of
    Left err -> assertFailure ("expected renamed obligation to elaborate and check: " <> T.unpack err)
    Right () -> pure ()

testCoproductObligationRawModalityRenameElaborates :: Assertion
testCoproductObligationRawModalityRenameElaborates = do
  let mode = ModeName "M"
  let modF = ModName "F"
  let fExpr = ModExpr { meSrc = mode, meTgt = mode, mePath = [modF] }
  let aVar = tvar mode "A"
  let genK =
        GenDecl
          { gdName = GenName "k"
          , gdMode = mode
          , gdParams = [GP_Ty (aVar)]
          , gdDom = [InPort (OVar aVar)]
          , gdCod = [OVar aVar]
          , gdLiteralKind = Nothing
          }
  let actionF =
        ModAction
          { maMod = modF
          , maGenMap = M.singleton (mode, GenName "k") (idD mode [OMod fExpr (OVar aVar)])
          , maPolicy = UseAllOriented
          }
  let rawExpr =
        PolyAST.ROETensor
          (PolyAST.ROEDiag (PolyAST.RDGen "k" (Just [PolyAST.RGPos (PolyAST.RPTVar "A")]) Nothing))
          ( PolyAST.ROETensor
              (PolyAST.ROEMap (PolyAST.RMComp ["F"]) (PolyAST.ROEDiag (PolyAST.RDId [PolyAST.RPTVar "A"])))
              ( PolyAST.ROETensor
                  ( PolyAST.ROEDiag
                      ( PolyAST.RDMap
                          (PolyAST.RMComp ["F"])
                          (PolyAST.RDId [PolyAST.RPTMod (PolyAST.RMComp ["F"]) (PolyAST.RPTVar "A")])
                      )
                  )
                  ( PolyAST.ROEDiag
                      ( PolyAST.RDMap
                          (PolyAST.RMComp ["F"])
                          ( PolyAST.RDId
                              [ PolyAST.RPTCon
                                  PolyAST.RawTypeRef
                                    { PolyAST.rtrMode = Nothing
                                    , PolyAST.rtrName = "F"
                                    }
                                  [PolyAST.RPTVar "A"]
                              ]
                          )
                      )
                  )
              )
          )
  let fa = OMod fExpr (OVar aVar)
  let ffa = OMod fExpr fa
  let obl =
        ObligationDecl
          { obName = "raw_mod_refl"
          , obMode = mode
          , obForGen = False
          , obForGenName = Nothing
          , obGenerated = False
          , obParams = map GP_Ty [aVar] <> map GP_Tm []
          , obDom = [OVar aVar, fa, ffa, ffa]
          , obCod = [OVar aVar, fa, ffa, ffa]
          , obLHSExpr = rawExpr
          , obRHSExpr = rawExpr
          , obPolicy = UseAllOriented
          }
  let mt =
        (mkModes (S.singleton mode))
          { mtDecls =
              M.singleton
                modF
                ModDecl
                  { mdName = modF
                  , mdSrc = mode
                  , mdTgt = mode
                  }
          }
  let docA =
        Doctrine
          { dName = "DocRawA"
          , dModes = mt
          , dAcyclicModes = S.empty
          , dGens = M.singleton mode (M.singleton (GenName "k") genK)
          , dCells2 = []
          , dActions = M.singleton modF actionF
          , dObligations = [obl]
                    }
  let docB =
        Doctrine
          { dName = "DocRawB"
          , dModes = mt
          , dAcyclicModes = S.empty
          , dGens = M.empty
          , dCells2 = []
          , dActions = M.empty
          , dObligations = []
                    }
  case validateDoctrine docA of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  case validateDoctrine docB of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  out <- case computePolyCoproduct "POblRawRen" docA docB of
    Left err -> assertFailure (T.unpack err)
    Right res -> pure (poDoctrine res)
  genMap <-
    fmap M.fromList $
      mapM
        ( \(mode', genDecl) -> do
            diag <- case genD mode' (gdPlainDom genDecl) (gdCod genDecl) (gdName genDecl) of
              Left err -> assertFailure (T.unpack err) >> error "unreachable"
              Right outDiag -> pure outDiag
            pure ((mode', gdName genDecl), plainImage diag)
        )
        [ (mode', genDecl)
        | (mode', table) <- M.toList (dGens out)
        , genDecl <- M.elems table
        ]
  let idMorph =
        Morphism
          { morName = "POblRawRen.id"
          , morSrc = out
          , morTgt = out
          , morIsCoercion = True
          , morModeMap = identityModeMap out
          , morModMap = identityModMap out
          , morTypeMap = M.empty
          , morGenMap = genMap
          , morCheck = CheckNone
          , morPolicy = UseAllOriented
          }
  case checkImplementsObligations emptyEnv out idMorph out of
    Left err -> assertFailure ("expected raw modality obligation to rename and check: " <> T.unpack err)
    Right () -> pure ()

testCoproductTransformCollisionRenames :: Assertion
testCoproductTransformCollisionRenames = do
  let mode = ModeName "M"
  let aVar = tvar mode "a"
  let witness =
        GenDecl
          { gdName = GenName "w"
          , gdMode = mode
          , gdParams = [GP_Ty (aVar)]
          , gdDom = [InPort (OVar aVar)]
          , gdCod = [OVar aVar]
          , gdLiteralKind = Nothing
          }
  let idMod = ModExpr { meSrc = mode, meTgt = mode, mePath = [] }
  let etaDecl =
        ModTransformDecl
          { mtdName = ModTransformName "eta"
          , mtdFrom = idMod
          , mtdTo = idMod
          , mtdWitness = GenName "w"
          }
  let mt =
        (mkModes (S.singleton mode))
          { mtTransforms = M.singleton (ModTransformName "eta") etaDecl
          }
  let mkDoc name =
        Doctrine
          { dName = name
          , dModes = mt
          , dAcyclicModes = S.empty
          , dGens = M.singleton mode (M.singleton (GenName "w") witness)
          , dCells2 = []
          , dActions = M.empty
          , dObligations = []
                    }
  let docA = mkDoc "LeftTr"
  let docB = mkDoc "RightTr"
  case validateDoctrine docA of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  case validateDoctrine docB of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  res <- case computePolyCoproduct "PTrCollide" docA docB of
    Left err -> assertFailure (T.unpack err)
    Right out -> pure out
  let outDoc = poDoctrine res
  let transforms = mtTransforms (dModes outDoc)
  M.size transforms @?= 2
  assertBool "expected right eta transform name to be preserved in coproduct" (M.member (ModTransformName "eta") transforms)
  assertBool "expected one additional renamed transform" (S.size (S.delete (ModTransformName "eta") (M.keysSet transforms)) == 1)
  mapM_
    ( \decl ->
        let witnessMode = meTgt (mtdFrom decl)
            gensAtMode = M.findWithDefault M.empty witnessMode (dGens outDoc)
        in assertBool "expected transform witness generator to exist in output doctrine" (M.member (mtdWitness decl) gensAtMode)
    )
    (M.elems transforms)

testApplyPushoutAcceptsNonCheckAllGlue :: Assertion
testApplyPushoutAcceptsNonCheckAllGlue = do
  let mode = ModeName "M"
  let aTy = tcon mode "A" []
  let genSrc =
        GenDecl
          { gdName = GenName "f"
          , gdMode = mode
          , gdParams = []
          , gdDom = [InPort aTy]
          , gdCod = [aTy]
          , gdLiteralKind = Nothing
          }
  lhs <- require (genD mode [aTy] [aTy] (GenName "f"))
  let srcCell =
        Cell2
          { c2Name = "eq"
          , c2Class = Structural
          , c2Orient = LR
          , c2Params = []
          , c2LHS = lhs
          , c2RHS = idD mode [aTy]
          }
  let src =
        withSelfClassifiedCtors
          [(mode, [(ObjName "A", [])])]
          Doctrine
            { dName = "SchemaApply"
            , dModes = mkModes (S.singleton mode)
            , dAcyclicModes = S.empty
            , dGens = M.fromList [(mode, M.fromList [(GenName "f", genSrc)])]
            , dCells2 = [srcCell]
            , dActions = M.empty
            , dObligations = []
                        }
  let body =
        withSelfClassifiedCtors
          [(mode, [(ObjName "A", [])])]
          Doctrine
            { dName = "BodyApply"
            , dModes = mkModes (S.singleton mode)
            , dAcyclicModes = S.empty
            , dGens = M.fromList [(mode, M.fromList [(GenName "f", genSrc)])]
            , dCells2 = []
            , dActions = M.empty
            , dObligations = []
                        }
  let genTgt =
        GenDecl
          { gdName = GenName "g"
          , gdMode = mode
          , gdParams = []
          , gdDom = [InPort aTy]
          , gdCod = [aTy]
          , gdLiteralKind = Nothing
          }
  let target =
        withSelfClassifiedCtors
          [(mode, [(ObjName "A", [])])]
          Doctrine
            { dName = "TargetApply"
            , dModes = mkModes (S.singleton mode)
            , dAcyclicModes = S.empty
            , dGens = M.fromList [(mode, M.fromList [(GenName "g", genTgt)])]
            , dCells2 = []
            , dActions = M.empty
            , dObligations = []
                        }
  case validateDoctrine src of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  case validateDoctrine body of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  case validateDoctrine target of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  imgF <- require (genD mode [aTy] [aTy] (GenName "f"))
  imgG <- require (genD mode [aTy] [aTy] (GenName "g"))
  let incl =
        Morphism
          { morName = "inclApply"
          , morSrc = src
          , morTgt = body
          , morIsCoercion = False
          , morModeMap = identityModeMap src
          , morModMap = identityModMap src
          , morTypeMap = M.empty
          , morGenMap = M.fromList [((mode, GenName "f"), plainImage imgF)]
          , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  let impl =
        Morphism
          { morName = "implApply"
          , morSrc = src
          , morTgt = target
          , morIsCoercion = False
          , morModeMap = identityModeMap src
          , morModMap = identityModMap src
          , morTypeMap = M.empty
          , morGenMap = M.fromList [((mode, GenName "f"), plainImage imgG)]
          , morCheck = CheckStructural
          , morPolicy = UseAllOriented
          }
  res <- case computePolyPushoutPreferRight "PApply" "FunctorF" incl impl of
    Left err -> assertFailure (T.unpack err)
    Right out -> pure out
  morCheck (poGlue res) @?= CheckStructural

testApplyPushoutTypeGenCollisionAfterModeRename :: Assertion
testApplyPushoutTypeGenCollisionAfterModeRename = do
  let modeI1 = ModeName "I1"
  let modeI2 = ModeName "I2"
  let modeL1 = ModeName "L1"
  let modeL2 = ModeName "L2"
  let modeM = ModeName "M"
  let source =
        Doctrine
          { dName = "SrcTypeGenCollapse"
          , dModes = mkModes (S.fromList [modeI1, modeI2])
          , dAcyclicModes = S.empty
          , dGens = M.empty
          , dCells2 = []
          , dActions = M.empty
          , dObligations = []
                    }
  let cL2 = tcon modeL2 "C" []
  let genL1 =
        GenDecl
          { gdName = GenName "g"
          , gdMode = modeL1
          , gdParams = []
          , gdDom = []
          , gdCod = []
          , gdLiteralKind = Nothing
          }
  let genL2 =
        GenDecl
          { gdName = GenName "g"
          , gdMode = modeL2
          , gdParams = []
          , gdDom = [InPort cL2]
          , gdCod = [cL2]
          , gdLiteralKind = Nothing
          }
  let body =
        withSelfClassifiedCtors
          [ (modeL1, [(ObjName "B", [])])
          , (modeL2, [(ObjName "B", []), (ObjName "C", [])])
          ]
          Doctrine
            { dName = "BodyTypeGenCollapse"
            , dModes = mkModes (S.fromList [modeL1, modeL2])
            , dAcyclicModes = S.empty
            , dGens =
                M.fromList
                  [ (modeL1, M.singleton (GenName "g") genL1)
                  , (modeL2, M.singleton (GenName "g") genL2)
                  ]
            , dCells2 = []
            , dActions = M.empty
            , dObligations = []
                        }
  let target =
        Doctrine
          { dName = "TargetTypeGenCollapse"
          , dModes = mkModes (S.singleton modeM)
          , dAcyclicModes = S.empty
          , dGens = M.empty
          , dCells2 = []
          , dActions = M.empty
          , dObligations = []
                    }
  mapM_ (either (assertFailure . T.unpack) pure . validateDoctrine) [source, body, target]
  let incl =
        Morphism
          { morName = "inclTypeGenCollapse"
          , morSrc = source
          , morTgt = body
          , morIsCoercion = False
          , morModeMap = M.fromList [(modeI1, modeL1), (modeI2, modeL2)]
          , morModMap = M.empty
          , morTypeMap = M.empty
          , morGenMap = M.empty
          , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  let impl =
        Morphism
          { morName = "implTypeGenCollapse"
          , morSrc = source
          , morTgt = target
          , morIsCoercion = False
          , morModeMap = M.fromList [(modeI1, modeM), (modeI2, modeM)]
          , morModMap = M.empty
          , morTypeMap = M.empty
          , morGenMap = M.empty
          , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  case computePolyPushoutPreferRight "PTypeGenCollapse" "TypeGenFocus" incl impl of
    Left err ->
      assertBool
        ("expected comprehension-witness mismatch under apply mode collapse, got: " <> T.unpack err)
        ("comprehension witness mismatch" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected strict apply pushout to reject mode collapse with divergent comprehension witnesses"

testApplyPushoutCellCollisionAfterModeRename :: Assertion
testApplyPushoutCellCollisionAfterModeRename = do
  let modeI = ModeName "I"
  let modeL = ModeName "L"
  let modeM = ModeName "M"
  let tyL = tcon modeL "A" []
  let tyM = tcon modeM "A" []
  let src =
        Doctrine
          { dName = "IfaceModeRename"
          , dModes = mkModes (S.singleton modeI)
          , dAcyclicModes = S.empty
          , dGens = M.empty
          , dCells2 = []
          , dActions = M.empty
          , dObligations = []
                    }
  bodyF <- require (genD modeL [tyL] [tyL] (GenName "f"))
  bodyG <- require (genD modeL [tyL] [tyL] (GenName "g"))
  let bodyCell =
        Cell2
          { c2Name = "eq"
          , c2Class = Computational
          , c2Orient = LR
          , c2Params = []
          , c2LHS = bodyF
          , c2RHS = bodyG
          }
  let body =
        withSelfClassifiedCtors
          [(modeL, [(ObjName "A", [])])]
          Doctrine
            { dName = "BodyModeRename"
            , dModes = mkModes (S.singleton modeL)
            , dAcyclicModes = S.empty
            , dGens =
                M.singleton
                  modeL
                  ( M.fromList
                      [ (GenName "f", GenDecl (GenName "f") modeL [] [InPort tyL] [tyL] Nothing)
                      , (GenName "g", GenDecl (GenName "g") modeL [] [InPort tyL] [tyL] Nothing)
                      ]
                  )
            , dCells2 = [bodyCell]
            , dActions = M.empty
            , dObligations = []
                        }
  targetF <- require (genD modeM [tyM] [tyM] (GenName "f"))
  targetG <- require (genD modeM [tyM] [tyM] (GenName "g"))
  let targetCell =
        Cell2
          { c2Name = "eq"
          , c2Class = Computational
          , c2Orient = LR
          , c2Params = []
          , c2LHS = targetG
          , c2RHS = targetF
          }
  let target =
        withSelfClassifiedCtors
          [(modeM, [(ObjName "A", [])])]
          Doctrine
            { dName = "TargetModeRename"
            , dModes = mkModes (S.singleton modeM)
            , dAcyclicModes = S.empty
            , dGens =
                M.singleton
                  modeM
                  ( M.fromList
                      [ (GenName "f", GenDecl (GenName "f") modeM [] [InPort tyM] [tyM] Nothing)
                      , (GenName "g", GenDecl (GenName "g") modeM [] [InPort tyM] [tyM] Nothing)
                      ]
                  )
            , dCells2 = [targetCell]
            , dActions = M.empty
            , dObligations = []
                        }
  mapM_ (either (assertFailure . T.unpack) pure . validateDoctrine) [src, body, target]
  let incl =
        Morphism
          { morName = "inclModeRename"
          , morSrc = src
          , morTgt = body
          , morIsCoercion = False
          , morModeMap = M.singleton modeI modeL
          , morModMap = M.empty
          , morTypeMap = M.empty
          , morGenMap = M.empty
          , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  let impl =
        Morphism
          { morName = "implModeRename"
          , morSrc = src
          , morTgt = target
          , morIsCoercion = False
          , morModeMap = M.singleton modeI modeM
          , morModMap = M.empty
          , morTypeMap = M.empty
          , morGenMap = M.empty
          , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  case computePolyPushoutPreferRight "PApplyModeCell" "FunctorF" incl impl of
    Left err ->
      assertBool
        ("expected comprehension-witness mismatch under colliding mode rename, got: " <> T.unpack err)
        ("comprehension witness mismatch" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected strict apply pushout to reject colliding mode renames with divergent comprehension witnesses"

testApplyPushoutModeCollapseUniverseDefEq :: Assertion
testApplyPushoutModeCollapseUniverseDefEq = do
  let modeI1 = ModeName "I1"
      modeI2 = ModeName "I2"
      modeL1 = ModeName "L1"
      modeL2 = ModeName "L2"
      modeM = ModeName "M"
      mkCompOnlySelfClassified name modes =
        let mt0 = mkModes (S.fromList modes)
            mt1 =
              mt0
                { mtClassifiedBy =
                    M.fromList
                      [ ( mode
                        , ClassificationDecl
                            { cdClassifier = mode
                            , cdUniverse = defaultUniverseObj mode
                            
                            , cdComp = Just compDecl
                            }
                        )
                      | mode <- modes
                      ]
                }
            gens =
              foldl
                (\acc mode -> insertCompSupportGens mode (defaultUniverseObj mode) acc)
                M.empty
                modes
         in Doctrine
              { dName = name
              , dModes = mt1
              , dAcyclicModes = S.empty
              , dGens = gens
              , dCells2 = []
              , dActions = M.empty
              , dObligations = []
                            }
      source = mkCompOnlySelfClassified "SrcCollapseDefEq" [modeI1, modeI2]
      body0 = mkCompOnlySelfClassified "BodyCollapseDefEq" [modeL1, modeL2]
      modeTheoryBody0 = dModes body0
      classDeclsBody0 = mtClassifiedBy modeTheoryBody0
      idL2 = ModExpr { meSrc = modeL2, meTgt = modeL2, mePath = [] }
      l2UniverseWrapped = OMod idL2 (defaultUniverseObj modeL2)
      body =
        body0
          { dModes =
              modeTheoryBody0
                { mtClassifiedBy =
                    M.adjust (\decl -> decl { cdUniverse = l2UniverseWrapped }) modeL2 classDeclsBody0
                }
          }
      target = mkCompOnlySelfClassified "TargetCollapseDefEq" [modeM]
  mapM_ (either (assertFailure . T.unpack) pure . validateDoctrine) [source, body, target]
  let incl =
        Morphism
          { morName = "inclCollapseDefEq"
          , morSrc = source
          , morTgt = body
          , morIsCoercion = False
          , morModeMap = M.fromList [(modeI1, modeL1), (modeI2, modeL2)]
          , morModMap = M.empty
          , morTypeMap = M.empty
          , morGenMap = M.empty
          , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
      impl =
        Morphism
          { morName = "implCollapseDefEq"
          , morSrc = source
          , morTgt = target
          , morIsCoercion = False
          , morModeMap = M.fromList [(modeI1, modeM), (modeI2, modeM)]
          , morModMap = M.empty
          , morTypeMap = M.empty
          , morGenMap = M.empty
          , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  case computePolyPushoutPreferRight "PApplyModeCollapseUniverseDefEq" "FunctorF" incl impl of
    Left err ->
      assertFailure
        ( "expected apply pushout to accept defeq universes under mode collapse, got: "
            <> T.unpack err
        )
    Right _ -> pure ()

testPushoutCellTmAlphaEq :: Assertion
testPushoutCellTmAlphaEq = do
  let modeM = ModeName "M"
  let modeI = ModeName "I"
  let natTy = mkCon (ObjRef modeI (ObjName "Nat")) []
  let vecRef = ObjRef modeM (ObjName "Vec")
  let genName = GenName "f"
  let mkTm name = TmVar { tmvName = name, tmvSort = natTy, tmvScope = 0, tmvOwnerMode = Nothing }
  let vecTy tmVar = mkCon vecRef [OATm (tmMeta tmVar)]
  let srcTm = mkTm "n"
  let leftTm = mkTm "i"
  let rightTm = mkTm "j"
  let zDecl =
        GenDecl
          { gdName = GenName "Z"
          , gdMode = modeI
          , gdParams = []
          , gdDom = []
          , gdCod = [natTy]
          , gdLiteralKind = Nothing
          }
  let srcGen =
        GenDecl
          { gdName = genName
          , gdMode = modeM
          , gdParams = [GP_Tm srcTm]
          , gdDom = [InPort (vecTy srcTm)]
          , gdCod = [vecTy srcTm]
          , gdLiteralKind = Nothing
          }
  let leftGen =
        GenDecl
          { gdName = genName
          , gdMode = modeM
          , gdParams = [GP_Tm leftTm]
          , gdDom = [InPort (vecTy leftTm)]
          , gdCod = [vecTy leftTm]
          , gdLiteralKind = Nothing
          }
  let rightGen =
        GenDecl
          { gdName = genName
          , gdMode = modeM
          , gdParams = [GP_Tm rightTm]
          , gdDom = [InPort (vecTy rightTm)]
          , gdCod = [vecTy rightTm]
          , gdLiteralKind = Nothing
          }
  leftLHS <- require (genericGenDiagram leftGen)
  rightLHS <- require (genericGenDiagram rightGen)
  let leftCell =
        Cell2
          { c2Name = "eqLeftTm"
          , c2Class = Computational
          , c2Orient = LR
          , c2Params = map GP_Ty [] <> map GP_Tm [leftTm]
          , c2LHS = leftLHS
          , c2RHS = idD modeM [vecTy leftTm]
          }
  let rightCell =
        Cell2
          { c2Name = "eqRightTm"
          , c2Class = Computational
          , c2Orient = LR
          , c2Params = map GP_Ty [] <> map GP_Tm [rightTm]
          , c2LHS = rightLHS
          , c2RHS = idD modeM [vecTy rightTm]
          }
  let commonDoc name gen cell =
        withSelfClassifiedCtors
          [ (modeI, [(ObjName "Nat", [])])
          , (modeM, [(ObjName "Vec", [TPS_Tm natTy])])
          ]
          Doctrine
            { dName = name
            , dModes = mkModes (S.fromList [modeM, modeI])
            , dAcyclicModes = S.empty
            , dGens =
                M.fromList
                  [ (modeI, M.fromList [(GenName "Z", zDecl)])
                  , (modeM, M.fromList [(genName, gen)])
                  ]
            , dCells2 = cell
            , dActions = M.empty
            , dObligations = []
                        }
  let src = commonDoc "SrcTmAlpha" srcGen []
  let left = commonDoc "LeftTmAlpha" leftGen [leftCell]
  let right = commonDoc "RightTmAlpha" rightGen [rightCell]
  case validateDoctrine src of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  case validateDoctrine left of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  case validateDoctrine right of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  img <- require (identityGenImage srcGen)
  zImg <- require (identityGenImage zDecl)
  let morLeft =
        Morphism
          { morName = "fTmAlpha"
          , morSrc = src
          , morTgt = left
          , morIsCoercion = False
          , morModeMap = identityModeMap src
          , morModMap = identityModMap src
          , morTypeMap = M.empty
          , morGenMap =
              M.fromList
                [ ((modeI, GenName "Z"), zImg)
                , ((modeM, genName), img)
                ]
        , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  let morRight =
        Morphism
          { morName = "gTmAlpha"
          , morSrc = src
          , morTgt = right
          , morIsCoercion = False
          , morModeMap = identityModeMap src
          , morModMap = identityModMap src
          , morTypeMap = M.empty
          , morGenMap =
              M.fromList
                [ ((modeI, GenName "Z"), zImg)
                , ((modeM, genName), img)
                ]
        , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  res <- case computePolyPushout "PTmAlpha" morLeft morRight of
    Left err -> assertFailure (T.unpack err)
    Right out -> pure out
  length (dCells2 (poDoctrine res)) @?= 1

testPushoutInjectionPreservesBinderArgs :: Assertion
testPushoutInjectionPreservesBinderArgs = do
  let mode = ModeName "M"
  let aTy = mkCon (ObjRef mode (ObjName "A")) []
  let gName = GenName "g"
  let slotSig = BinderSig { bsTmCtx = [], bsDom = [aTy], bsCod = [aTy] }
  let gDecl =
        GenDecl
          { gdName = gName
          , gdMode = mode
          , gdParams = []
          , gdDom = [InBinder slotSig]
          , gdCod = [aTy]
          , gdLiteralKind = Nothing
          }
  let iface =
        Doctrine
          { dName = "IfaceBinder"
          , dModes = mkModes (S.singleton mode)
    , dAcyclicModes = S.empty
          , dGens = M.empty
          , dCells2 = []
      , dActions = M.empty
      , dObligations = []
                    }
  let left =
        attachComprehensionFixture mode aTy $
          withSelfClassifiedCtors
            [(mode, [(ObjName "A", [])])]
            iface
              { dName = "LeftBinder"
              , dGens = M.fromList [(mode, M.fromList [(gName, gDecl)])]
              }
  let right = iface { dName = "RightBinder" }
  case validateDoctrine iface of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  case validateDoctrine left of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  case validateDoctrine right of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  let mkIfaceIn name tgt =
        Morphism
          { morName = name
          , morSrc = iface
          , morTgt = tgt
          , morIsCoercion = False
          , morModeMap = identityModeMap iface
          , morModMap = identityModMap iface
          , morTypeMap = M.empty
          , morGenMap = M.empty
        , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  let morLeft = mkIfaceIn "iface.left" left
  let morRight = mkIfaceIn "iface.right" right
  res <- case computePolyPushout "PBindInj" morLeft morRight of
    Left err -> assertFailure (T.unpack err)
    Right out -> pure out
  let body = idD mode [aTy]
  leftDiag0 <- require (genD mode [] [aTy] gName)
  leftDiag <- require (setSingleEdgeBargs leftDiag0 [BAConcrete body])
  mapped <- case applyMorphismDiagram (poInl res) leftDiag of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  case IM.elems (dEdges mapped) of
    [Edge _ (PGen _ _ [BAConcrete _]) _ _] -> pure ()
    _ -> assertFailure "expected mapped injection image to preserve one concrete binder argument"

testPushoutAcceptsRenamingWithBinders :: Assertion
testPushoutAcceptsRenamingWithBinders = do
  let mode = ModeName "M"
  let aRef = ObjRef mode (ObjName "A")
  let a1Ref = ObjRef mode (ObjName "A1")
  let aTy = mkCon aRef []
  let a1Ty = mkCon a1Ref []
  let gName = GenName "g"
  let g1Name = GenName "g1"
  let slotSigSrc = BinderSig { bsTmCtx = [], bsDom = [aTy], bsCod = [aTy] }
  let slotSigTgt = BinderSig { bsTmCtx = [], bsDom = [a1Ty], bsCod = [a1Ty] }
  let ifaceGen =
        GenDecl
          { gdName = gName
          , gdMode = mode
          , gdParams = []
          , gdDom = [InBinder slotSigSrc]
          , gdCod = [aTy]
          , gdLiteralKind = Nothing
          }
  let leftGen =
        GenDecl
          { gdName = g1Name
          , gdMode = mode
          , gdParams = []
          , gdDom = [InBinder slotSigTgt]
          , gdCod = [a1Ty]
          , gdLiteralKind = Nothing
          }
  let iface =
        attachComprehensionFixture mode aTy $
          withSelfClassifiedCtors
            [(mode, [(ObjName "A", [])])]
            Doctrine
              { dName = "IfaceRenameBinder"
              , dModes = mkModes (S.singleton mode)
              , dAcyclicModes = S.empty
              , dGens = M.fromList [(mode, M.fromList [(gName, ifaceGen)])]
              , dCells2 = []
              , dActions = M.empty
              , dObligations = []
                            }
  let left =
        attachComprehensionFixture mode a1Ty $
          withSelfClassifiedCtors
            [(mode, [(ObjName "A1", [])])]
            Doctrine
              { dName = "LeftRenameBinder"
              , dModes = mkModes (S.singleton mode)
              , dAcyclicModes = S.empty
              , dGens = M.fromList [(mode, M.fromList [(g1Name, leftGen)])]
              , dCells2 = []
              , dActions = M.empty
              , dObligations = []
                            }
  let right = iface { dName = "RightRenameBinder" }
  case validateDoctrine iface of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  case validateDoctrine left of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  case validateDoctrine right of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  let hole = BinderMetaVar "b0"
  imgLeft0 <- require (genD mode [] [a1Ty] g1Name)
  imgLeft <- require (setSingleEdgeBargs imgLeft0 [BAMeta hole])
  imgRight0 <- require (genD mode [] [aTy] gName)
  imgRight <- require (setSingleEdgeBargs imgRight0 [BAMeta hole])
  compImgsLeft <- require (compIdentityImages mode a1Ty)
  compImgsRight <- require (compIdentityImages mode aTy)
  let morLeft =
        Morphism
          { morName = "fRenameBinder"
          , morSrc = iface
          , morTgt = left
          , morIsCoercion = False
          , morModeMap = identityModeMap iface
          , morModMap = identityModMap iface
          , morTypeMap = M.fromList [(aRef, TypeTemplate [] a1Ty)]
          , morGenMap =
              M.fromList
                ([((mode, gName), GenImage imgLeft (M.fromList [(hole, slotSigTgt)]))]
                  <> compImgsLeft)
        , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  let morRight =
        Morphism
          { morName = "gRenameBinder"
          , morSrc = iface
          , morTgt = right
          , morIsCoercion = False
          , morModeMap = identityModeMap iface
          , morModMap = identityModMap iface
          , morTypeMap = M.empty
          , morGenMap =
              M.fromList
                ([((mode, gName), GenImage imgRight (M.fromList [(hole, slotSigSrc)]))]
                  <> compImgsRight)
        , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  case computePolyPushout "PRenameBinder" morLeft morRight of
    Left err -> assertFailure (T.unpack err)
    Right _ -> pure ()

mkModeEqTheory :: ModeName -> ModName -> ModName -> ModeTheory
mkModeEqTheory mode modF modU =
  ModeTheory
    { mtModes = M.singleton mode (ModeInfo { miName = mode, miDefEqEngine = DefEqTRS })
    , mtDecls =
        M.fromList
          [ (modF, ModDecl modF mode mode)
          , (modU, ModDecl modU mode mode)
          ]
    , mtEqns =
        [ ModEqn
            (ModExpr { meSrc = mode, meTgt = mode, mePath = [modF, modU] })
            (ModExpr { meSrc = mode, meTgt = mode, mePath = [] })
        ]
    , mtTransforms = M.empty
    , mtClassifiedBy = M.empty
    , mtClassifierLifts = M.empty
    }

mkModeEqMorph :: Text -> Doctrine -> Doctrine -> Text -> Morphism
mkModeEqMorph name src tgt varName =
  let mode = ModeName "M"
      hImg =
        case M.lookup mode (dGens tgt) >>= M.lookup (GenName "h") of
          Nothing -> error "mkModeEqMorph: missing h"
          Just gd ->
            case identityGenImage gd of
              Left _ -> error "mkModeEqMorph: identityGenImage h failed"
              Right img -> img
      modalImg =
        case M.lookup mode (dGens tgt) >>= M.lookup (GenName "modal") of
          Nothing -> error "mkModeEqMorph: missing modal"
          Just gd ->
            case identityGenImage gd of
              Left _ -> error "mkModeEqMorph: identityGenImage modal failed"
              Right img -> img
  in Morphism
      { morName = name
      , morSrc = src
      , morTgt = tgt
      , morIsCoercion = False
      , morModeMap = identityModeMap src
      , morModMap = identityModMap src
      , morTypeMap = M.empty
      , morGenMap = M.fromList [((mode, GenName "h"), hImg), ((mode, GenName "modal"), modalImg)]
        , morCheck = CheckAll
      , morPolicy = UseAllOriented
      }

mkModeEqDoctrine :: Text -> ModeTheory -> Text -> Bool -> Either Text Doctrine
mkModeEqDoctrine name mt varName useUF = do
  let mode = ModeName "M"
  let modF = ModName "F"
  let modU = ModName "U"
  let v = mkModeMetaVar varName mode
  let fExpr = ModExpr { meSrc = mode, meTgt = mode, mePath = [modF] }
  let ufExpr = ModExpr { meSrc = mode, meTgt = mode, mePath = [modF, modU] }
  let hTy =
        if useUF
          then OMod ufExpr (OVar v)
          else OVar v
  let modalTy = OMod fExpr (OVar v)
  let genH = GenDecl
        { gdName = GenName "h"
        , gdMode = mode
        , gdParams = [GP_Ty (v)]
        , gdDom = map InPort [OVar v]
        , gdCod = [OVar v]
        , gdLiteralKind = Nothing
        }
  let genModal = GenDecl
        { gdName = GenName "modal"
        , gdMode = mode
        , gdParams = [GP_Ty (v)]
        , gdDom = map InPort [modalTy]
        , gdCod = [modalTy]
        , gdLiteralKind = Nothing
        }
  lhs <- genericGenDiagram genH
  let cell = Cell2
        { c2Name = "eta"
        , c2Class = Computational
        , c2Orient = LR
        , c2Params = map GP_Ty [v] <> map GP_Tm []
        , c2LHS = lhs
        , c2RHS = idD mode [hTy]
        }
  let doc = Doctrine
        { dName = name
        , dModes = mt
    , dAcyclicModes = S.empty
        , dGens = M.fromList [(mode, M.fromList [(GenName "h", genH), (GenName "modal", genModal)])]
        , dCells2 = [cell]
      , dActions = M.empty
      , dObligations = []
                }
  case validateDoctrine doc of
    Left err -> Left err
    Right () -> Right doc

testPushoutRejectsIncompatibleClassifiedUniverses :: Assertion
testPushoutRejectsIncompatibleClassifiedUniverses = do
  let modeTy = ModeName "Ty"
      leftUniverse = mkCon (ObjRef modeTy (ObjName "U_TM_L")) []
      rightUniverse = mkCon (ObjRef modeTy (ObjName "U_TM_R")) []
  left <- require (mkClassifiedPushoutDoctrine "LeftClass" leftUniverse (ObjName "U_TM_L"))
  right <- require (mkClassifiedPushoutDoctrine "RightClass" rightUniverse (ObjName "U_TM_R"))
  let iface = mkClassifiedPushoutInterface
      morL = mkClassifiedPushoutMorph "leftIncl" iface left
      morR = mkClassifiedPushoutMorph "rightIncl" iface right
  case computePolyPushout "PClassUniverseConflict" morL morR of
    Left err ->
      assertBool
        ("expected universe mismatch rejection, got: " <> T.unpack err)
        ("universe mismatch" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected pushout to reject incompatible classified universes"

testPushoutAcceptsDefEqClassifiedUniverses :: Assertion
testPushoutAcceptsDefEqClassifiedUniverses = do
  let modeTy = ModeName "Ty"
      tmCtor = ObjName "U_TM_BASE"
      baseUniverse = mkCon (ObjRef modeTy tmCtor) []
      liftedUniverse = OMod ModExpr { meSrc = modeTy, meTgt = modeTy, mePath = [] } baseUniverse
  left <- require (mkClassifiedPushoutDoctrine "LeftDefEq" liftedUniverse tmCtor)
  right <- require (mkClassifiedPushoutDoctrine "RightDefEq" baseUniverse tmCtor)
  let iface = mkClassifiedPushoutInterface
      morL = mkClassifiedPushoutMorph "leftInclDefEq" iface left
      morR = mkClassifiedPushoutMorph "rightInclDefEq" iface right
  case computePolyPushout "PClassUniverseDefEq" morL morR of
    Left err ->
      assertFailure ("expected pushout with defeq classified universes to succeed: " <> T.unpack err)
    Right _ -> pure ()

mkClassifiedPushoutInterface :: Doctrine
mkClassifiedPushoutInterface =
  case mkClassifiedPushoutDoctrine "IfaceClass" baseUniverse (ObjName "U_TM_BASE") of
    Left err -> error ("mkClassifiedPushoutInterface: " <> T.unpack err)
    Right doc -> doc
  where
    modeTy = ModeName "Ty"
    baseUniverse = mkCon (ObjRef modeTy (ObjName "U_TM_BASE")) []

mkClassifiedPushoutDoctrine :: Text -> Obj -> ObjName -> Either Text Doctrine
mkClassifiedPushoutDoctrine name tmUniverse tmCtorName = do
  let modeTy = ModeName "Ty"
      modeTm = ModeName "Tm"
      uTy = mkCon (ObjRef modeTy (ObjName "U_TY")) []
      modeTheory =
        (mkModes (S.fromList [modeTy, modeTm]))
          { mtClassifiedBy =
              M.fromList
                [ ( modeTy
                  , ClassificationDecl
                      { cdClassifier = modeTy
                      , cdUniverse = uTy
                      
                      , cdComp = Just compDecl
                      }
                  )
                , ( modeTm
                  , ClassificationDecl
                      { cdClassifier = modeTy
                      , cdUniverse = tmUniverse
                      
                      , cdComp = Just compDecl
                      }
                  )
                ]
          }
      tyCtorNames =
        S.toList (S.fromList [ObjName "U_TY", ObjName "U_TM_BASE", tmCtorName])
      tyCtorDecls =
        [ ctorDecl uTy modeTy ctorName []
        | ctorName <- tyCtorNames
        ]
      tySupport =
        [ mkPolyCompGen modeTy uTy compCtxExtName
        , mkPolyCompGen modeTy uTy compVarName
        , mkPolyCompGen modeTy uTy compReindexName
        ]
      tmSupport =
        [ mkPolyCompGen modeTm tmUniverse compCtxExtName
        , mkPolyCompGen modeTm tmUniverse compVarName
        , mkPolyCompGen modeTm tmUniverse compReindexName
        ]
      tyTable = M.fromList [ (gdName gd, gd) | gd <- tyCtorDecls <> tySupport ]
      tmTable = M.fromList [ (gdName gd, gd) | gd <- tmSupport ]
      doc =
        Doctrine
          { dName = name
          , dModes = modeTheory
          , dAcyclicModes = S.empty
          , dGens = M.fromList [(modeTy, tyTable), (modeTm, tmTable)]
          , dCells2 = []
          , dActions = M.empty
          , dObligations = []
                    }
  case validateDoctrine doc of
    Left err -> Left err
    Right () -> Right doc

mkPolyCompGen :: ModeName -> Obj -> GenName -> GenDecl
mkPolyCompGen mode sortTy name =
  let a =
        TmVar
          { tmvName = "a"
          , tmvSort = sortTy
          , tmvScope = 0
          , tmvOwnerMode = Just mode
          }
   in GenDecl
        { gdName = name
        , gdMode = mode
        , gdParams = [GP_Ty a]
        , gdDom = [InPort (OVar (a))]
        , gdCod = [OVar (a)]
        , gdLiteralKind = Nothing
        }

mkClassifiedPushoutMorph :: Text -> Doctrine -> Doctrine -> Morphism
mkClassifiedPushoutMorph name src tgt =
  Morphism
    { morName = name
    , morSrc = src
    , morTgt = tgt
    , morIsCoercion = False
    , morModeMap = identityModeMap src
    , morModMap = identityModMap src
    , morTypeMap = M.empty
    , morGenMap = M.empty
    , morCheck = CheckNone
    , morPolicy = UseAllOriented
    }

mkTypeDoctrine :: ModeName -> Text -> [(ObjName, Int)] -> Either Text Doctrine
mkTypeDoctrine mode name types = do
  let sigs = [ (tname, replicate arity (TPS_Ty mode)) | (tname, arity) <- types ]
  let modeSet = S.singleton mode
  let doc =
        withSelfClassifiedCtors
          [(mode, sigs)]
          Doctrine
            { dName = name
            , dModes = selfClassifiedModes modeSet
            , dAcyclicModes = S.empty
            , dGens = M.empty
            , dCells2 = []
            , dActions = M.empty
            , dObligations = []
                        }
  case validateDoctrine doc of
    Left err -> Left err
    Right () -> Right doc
