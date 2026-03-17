{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
module Strat.Poly.Doctrine
  ( InputShape(..)
  , GenParam(..)
  , BinderSig(..)
  , GenDecl(..)
  , gdTyVars
  , gdTmVars
  , ModAction(..)
  , ObligationDecl(..)
  , obTyVars
  , obTmVars
  , BuiltinDecl(..)
  , BuiltinSpec(..)
  , BuiltinBranchDecl(..)
  , Doctrine(..)
  , CtorTables
  , gdPlainDom
  , isTypeDeclGenNameInTables
  , mkTypeTheory
  , doctrineTypeTheory
  , doctrineTypeTheoryFromTables
  , doctrineElabTypeTheoryFromTables
  , doctrineTypeTheoryBaseFromTables
  , deriveCtorTables
  , deriveCtorTablesForElab
  , allCtorSigsInTables
  , lookupCtorSigByRefInTables
  , lookupCtorSigForOwnerInTables
  , lookupCtorRefForOwnerInTables
  , lookupGenDeclInDoctrine
  , tmHeadSigForGenDecl
  , actionImageForGenerator
  , instantiateGenParams
  , genericGenDiagram
  , checkType
  , checkModTransformWitness
  , doctrineCheck
  , validateDoctrine
  , modeIsAcyclic
  ) where

import Data.Text (Text)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.IntMap.Strict as IM
import qualified Data.List as L
import qualified Data.Text as T
import Data.Bifunctor (first)
import Data.Maybe (catMaybes, listToMaybe, mapMaybe)
import Control.Monad (foldM, guard, forM)
import Strat.Poly.ModeTheory
import Strat.Poly.Alpha (canonicalizeCtorSig)
import Strat.Poly.Obj
import Strat.Poly.ObjClassifier (classifierOfMode, classifierModeForCtorUse, modeClassifierMode, modeUniverseObj)
import Strat.Poly.PendingUniverse (pendingUniverseSeedInnerRef)
import Strat.Poly.TypeTheory
  ( TypeTheory(..)
  , ttCtorTablesByOwner
  , DefFragment(..)
  , BinderSig(..)
  , BuiltinHeadRole(..)
  , FunctionBuiltin(..)
  , ExtensionalBuiltin(..)
  , RecursiveHeadArgSource(..)
  , BranchInputSource(..)
  , ElimBranchBuiltin(..)
  , InductiveElimBuiltin(..)
  , EliminatorBuiltin(..)
  , BuiltinHeads(..)
  , TmHeadSig(..)
  , GenArgSig(..)
  , TmRule(..)
  , emptyBuiltinHeads
  , emptyDefFragment
  , lookupTmHeadSig
  , termHeadsForMode
  )
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Literal
import Strat.Poly.Diagram
import Strat.Poly.DiagramInterpretation
  ( DiagramInterpretation(..)
  , applySubstBinderSig
  , applySubstBinderSigs
  , binderHoleCaptureRiskMetasDiagram
  , binderHoleNames
  , instantiateGenImageBindersWithMapper
  , interpretDiagram
  , renameBinderArgMetas
  , requirePortType
  , spliceEdge
  , stableHoleCaptureRenaming
  )
import Strat.Poly.DiagramBuild (allocPorts)
import Strat.Poly.Graph
  ( BinderArg(..)
  , BinderMetaVar(..)
  , Edge(..)
  , EdgePayload(..)
  , addEdgePayload
  , emptyDiagram
  , freshPort
  , unEdgeId
  , unPortId
  , validateDiagram
  )
import Strat.Poly.Cell2
import Strat.Poly.Tele (CtorSig(..), GenParam(..), teleDistinctNames, teleTyVars, teleTmVars)
import Strat.Poly.DSL.AST (RawOblExpr(..))
import Strat.Poly.Subst (Subst, codeBindings, emptySubst, mkSubst, tmBindings)
import Strat.Poly.Term.Compat (termDiagramOutputSort, unifyCtxCompat)
import Strat.Poly.Term.SubstRuntime (applySubstCtx, applySubstObj, composeSubst, normalizeSubst)
import Strat.Poly.UnifyFlex (unifyCtxDiagram, unifyCtx, unifyObjFlex)
import Strat.Common.Rules (RewritePolicy(..), RuleClass(..), Orientation(..))
import Strat.Poly.DefEq
  ( checkCodeWellFormed
  , termToDiagram
  , termExprToDiagramChecked
  , normalizeObjDeep
  , normalizeObjDeepWithCtx
  , defEqObj
  )
import Strat.Poly.Term.RewriteCompile (compileAllTermRules)
import Strat.Poly.Term.Termination (checkTerminatingSCT)
import Strat.Poly.Term.AST (TermExpr(..), TermHeadArg(..), TermBinderArg(..), pattern TMGen)
import Strat.Poly.Term.FragmentConfluence (checkTypeTheoryConfluenceWithMapper)
import Strat.Poly.Term.HeadInst
  ( instantiateStoredHeadSubst
  , instantiateStructuralBinderSig
  )
import Strat.Poly.TermExpr
  ( applyHeadSubstObj
  , diagramGraphToRuleExpr
  , instantiateHostBoundObj
  , instantiateHostBoundCtx
  , normalizeCtxStructurallyWithPrefix
  , structuralConvEnv
  )
import Strat.Poly.Term.RewriteSystem (TRS, mkTRS)
import qualified Strat.Poly.Term.RewriteSystem as RS

data InputShape
  = InPort Obj
  | InBinder BinderSig
  deriving (Eq, Ord, Read, Show)

data GenDecl = GenDecl
  { gdName :: GenName
  , gdMode :: ModeName
  , gdParams :: [GenParam]
  , gdDom :: [InputShape]
  , gdCod :: Context
  , gdLiteralKind :: Maybe LiteralKind
  } deriving (Eq, Read, Show)

gdTyVars :: GenDecl -> [TmVar]
gdTyVars = teleTyVars . gdParams

gdTmVars :: GenDecl -> [TmVar]
gdTmVars = teleTmVars . gdParams

data ModAction = ModAction
  { maMod :: ModName
  , maGenMap :: M.Map (ModeName, GenName) Diagram
  , maPolicy :: RewritePolicy
  } deriving (Eq, Read, Show)

data ObligationDecl = ObligationDecl
  { obName :: Text
  , obMode :: ModeName
  , obForGen :: Bool
  , obForGenName :: Maybe GenName
  , obGenerated :: Bool
  , obParams :: [GenParam]
  , obDom :: Context
  , obCod :: Context
  , obLHSExpr :: RawOblExpr
  , obRHSExpr :: RawOblExpr
  , obPolicy :: RewritePolicy
  } deriving (Eq, Read, Show)

obTyVars :: ObligationDecl -> [TmVar]
obTyVars
  =
  teleTyVars . obParams

obTmVars :: ObligationDecl -> [TmVar]
obTmVars
  =
  teleTmVars . obParams

data BuiltinDecl = BuiltinDecl
  { bdHead :: GenName
  , bdMode :: ModeName
  , bdSpec :: BuiltinSpec
  } deriving (Eq, Read, Show)

data BuiltinSpec
  = BDTransport
  | BDInductiveElim
      { bdsScrutineeIndex :: Int
      , bdsBranches :: [BuiltinBranchDecl]
      }
  deriving (Eq, Read, Show)

data BuiltinBranchDecl = BuiltinBranchDecl
  { bbdCtor :: GenName
  , bbdTmCtxInputs :: [BranchInputSource]
  , bbdInputs :: [BranchInputSource]
  } deriving (Eq, Read, Show)

type CtorTables = M.Map ModeName (M.Map ObjName CtorSig)

gdPlainDom :: GenDecl -> Context
gdPlainDom gd =
  [ ty
  | InPort ty <- gdDom gd
  ]

lookupGenDeclInDoctrine :: Text -> Doctrine -> ModeName -> GenName -> Either Text GenDecl
lookupGenDeclInDoctrine missingMsg doc mode genName =
  case M.lookup mode (dGens doc) >>= M.lookup genName of
    Nothing -> Left missingMsg
    Just gd -> Right gd

tmHeadSigForGenDecl :: GenDecl -> Maybe TmHeadSig
tmHeadSigForGenDecl gd =
  case gdCod gd of
    [res]
      ->
          Just
            TmHeadSig
              { thsParams = gdParams gd
              , thsInputs = [ ty | InPort ty <- gdDom gd ]
              , thsBinders = [ bs | InBinder bs <- gdDom gd ]
              , thsRes = res
              }
    _ ->
      Nothing

isTypeDeclGenNameInTables :: Doctrine -> CtorTables -> ModeName -> ObjName -> Bool
isTypeDeclGenNameInTables doc tables classifierMode ctorName =
  any
    (\(ownerMode, table) ->
        case classifierOfMode (dModes doc) ownerMode of
          Just decl ->
            cdClassifier decl == classifierMode
              && M.member ctorName table
          Nothing -> False
    )
    (M.toList tables)

data Doctrine = Doctrine
  { dName :: Text
  , dModes :: ModeTheory
  , dAcyclicModes :: S.Set ModeName
  , dGens :: M.Map ModeName (M.Map GenName GenDecl)
  , dCells2 :: [Cell2]
  , dBuiltins :: [BuiltinDecl]
  , dActions :: M.Map ModName ModAction
  , dObligations :: [ObligationDecl]
  } deriving (Eq, Read, Show)

doctrineTypeTheory :: Doctrine -> Either Text TypeTheory
doctrineTypeTheory = mkTypeTheory

mkTypeTheory :: Doctrine -> Either Text TypeTheory
mkTypeTheory doc = do
  ctorTables <- deriveCtorTables doc
  mkTypeTheoryFromTables doc ctorTables

doctrineTypeTheoryFromTables :: Doctrine -> CtorTables -> Either Text TypeTheory
doctrineTypeTheoryFromTables = mkTypeTheoryFromTables

doctrineElabTypeTheoryFromTables :: Doctrine -> CtorTables -> Either Text TypeTheory
doctrineElabTypeTheoryFromTables = mkElabTypeTheoryFromTables

mkTypeTheoryFromTables :: Doctrine -> CtorTables -> Either Text TypeTheory
mkTypeTheoryFromTables doc ctorTables = do
  tt0 <- doctrineTypeTheoryBaseFromTables doc ctorTables
  trs <- compileAllTermRules tt0
  fragments <- buildCompiledFragments doc tt0 trs
  let tt = tt0 { ttDefFragments = fragments }
  checkTypeTheoryConfluenceWithMapper (applyModExprWithTypeTheory tt doc) tt
  pure tt

mkElabTypeTheoryFromTables :: Doctrine -> CtorTables -> Either Text TypeTheory
mkElabTypeTheoryFromTables doc ctorTables = do
  tt0 <- doctrineTypeTheoryBaseFromTables doc ctorTables
  trs <- compileAllTermRules tt0
  fragments <- buildCtorEligibilityElabFragments doc tt0 trs
  pure (tt0 { ttDefFragments = fragments })

doctrineTypeTheoryBaseFromTables :: Doctrine -> CtorTables -> Either Text TypeTheory
doctrineTypeTheoryBaseFromTables doc ctorTables =
  let tmHeads = derivedTmHeads doc ctorTables
      genArgSigs = derivedGenArgSigs doc
      diagramRules = derivedDiagramRules doc
   in do
        tmRules <- derivedTmRules doc tmHeads
        let fragments0 = mkDefFragments (dModes doc) tmHeads tmRules diagramRules M.empty
        ctorSigs <- ctorSigEnvFromTables doc ctorTables
        pure
          TypeTheory
            { ttModes = dModes doc
            , ttCtorSigs = ctorSigs
            , ttUniverseCtors = universeCtorsFromTables ctorTables
            , ttLiteralKinds = literalKindsFromDoctrine doc ctorTables
            , ttGenArgSigs = genArgSigs
            , ttDefFragments = fragments0
            , ttStrictCtorLookup = True
            }
  where
    ctorSigEnvFromTables d tables =
      foldM insertOwner M.empty (M.toList tables)
      where
        insertOwner acc (ownerMode, table) =
          foldM (insertOne ownerMode) acc (M.toList table)
        insertOne ownerMode acc (ctorName, sig) =
          let classifierMode = modeClassifierMode (dModes d) ownerMode
              classifierTable = M.findWithDefault M.empty classifierMode acc
           in case M.lookup ctorName classifierTable of
                Nothing ->
                  Right
                    ( M.insert
                        classifierMode
                        (M.insert ctorName sig classifierTable)
                        acc
                    )
                Just sig0
                  | sig0 == sig ->
                      Right acc
                  | otherwise ->
                      Left
                        ( "constructor `"
                            <> unObjName ctorName
                            <> "` has conflicting signatures across owner modes for classifier "
                            <> renderMode classifierMode
                        )
    universeCtorsFromTables tables =
      M.map (S.fromList . M.keys) tables

    literalKindsFromDoctrine d _tables =
      M.fromList
        [ (ownerMode, declaredLiteralKinds ownerMode)
        | ownerMode <- M.keys (mtModes (dModes d))
        ]
      where
        declaredLiteralKinds ownerMode =
          M.fromList
            [ (ObjName ctorText, litKind)
            | genDecl <- M.elems (M.findWithDefault M.empty classifierMode (dGens d))
            , isCtorLikeGen genDecl
            , let GenName ctorText = gdName genDecl
            , Just litKind <- [gdLiteralKind genDecl]
            ]
          where
            classifierMode =
              case classifierOfMode (dModes d) ownerMode of
                Just classDecl -> cdClassifier classDecl
                Nothing -> ownerMode

mkDefFragments
  :: ModeTheory
  -> M.Map ModeName (M.Map GenName TmHeadSig)
  -> M.Map ModeName [TmRule]
  -> M.Map ModeName [Cell2]
  -> M.Map ModeName TRS
  -> M.Map ModeName DefFragment
mkDefFragments mt tmFuns tmRules diagramRules tmTRS =
  M.fromList
    [ (mode, mkOne mode)
    | mode <- M.keys (mtModes mt)
    ]
  where
    mkOne mode =
      DefFragment
        { dfMode = mode
        , dfHeads = M.findWithDefault M.empty mode tmFuns
        , dfRules = M.findWithDefault [] mode tmRules
        , dfDiagramRules = M.findWithDefault [] mode diagramRules
        , dfCompiledRules = M.findWithDefault (mkTRS mode []) mode tmTRS
        , dfBuiltins = emptyBuiltinHeads
        }

checkFragmentTermination :: DefFragment -> Either Text ()
checkFragmentTermination fragment =
  case checkTerminatingSCT (dfCompiledRules fragment) of
    Right () -> Right ()
    Left err ->
      let trs = dfCompiledRules fragment
       in Left
            ( err
                <> "\n  root symbols: "
                <> renderRootSymbols trs
                <> "\n  fragment rules:\n"
                <> renderFragmentRules trs
            )

renderModeNameText :: ModeName -> Text
renderModeNameText (ModeName n) = n

renderGenNameText :: GenName -> Text
renderGenNameText (GenName n) = n

renderObjNameText :: ObjName -> Text
renderObjNameText (ObjName n) = n

normalizeMaybe :: ModeTheory -> Obj -> Maybe Obj
normalizeMaybe mt ty = either (const Nothing) Just (normalizeObjExpr mt ty)

matchBinaryCon
  :: ModeTheory
  -> ModeName
  -> Obj
  -> Maybe (ObjName, Obj, Obj)
matchBinaryCon mt expectedClassifier ty = do
  ty' <- normalizeMaybe mt ty
  case objCode ty' of
    CTCon ref [CAObj a, CAObj b]
      | orMode ref == expectedClassifier -> do
          a' <- normalizeMaybe mt a
          b' <- normalizeMaybe mt b
          Just (orName ref, a', b')
    _ -> Nothing

inferFunctionHeadEta :: [GenParam] -> Maybe Bool
inferFunctionHeadEta params =
  case params of
    [] -> Just False
    [GP_Ty _, GP_Ty _] -> Just True
    _ -> Nothing

inferLamBuiltinHead :: ModeTheory -> ModeName -> TmHeadSig -> Maybe ObjName
inferLamBuiltinHead mt classifierMode sig = do
  guard (null (thsInputs sig))
  guard (length (thsBinders sig) == 1)
  _ <- inferFunctionHeadEta (thsParams sig)
  bs <- case thsBinders sig of
    [one] -> Just one
    _ -> Nothing
  guard (length (bsDom bs) == 1)
  guard (length (bsCod bs) == 1)
  aTy0 <- case bsDom bs of
    [a] -> Just a
    _ -> Nothing
  bTy0 <- case bsCod bs of
    [b] -> Just b
    _ -> Nothing
  aTy <- normalizeMaybe mt aTy0
  bTy <- normalizeMaybe mt bTy0
  resTy <- normalizeMaybe mt (thsRes sig)
  (arrName, domTy, codTy) <- matchBinaryCon mt classifierMode resTy
  guard (domTy == aTy)
  guard (codTy == bTy)
  pure arrName

inferLamBuiltinCandidate :: ModeTheory -> ModeName -> TmHeadSig -> Maybe (ObjName, Bool)
inferLamBuiltinCandidate mt classifierMode sig = do
  arrName <- inferLamBuiltinHead mt classifierMode sig
  etaCapable <- inferFunctionHeadEta (thsParams sig)
  pure (arrName, etaCapable)

inferAppBuiltinHead :: ModeTheory -> ModeName -> TmHeadSig -> Maybe ObjName
inferAppBuiltinHead mt classifierMode sig = do
  guard (null (thsBinders sig))
  guard (length (thsInputs sig) == 2)
  _ <- inferFunctionHeadEta (thsParams sig)
  (funTy0, argTy0) <- case thsInputs sig of
    [funTy, argTy] -> Just (funTy, argTy)
    _ -> Nothing
  funTy <- normalizeMaybe mt funTy0
  argTy <- normalizeMaybe mt argTy0
  resTy <- normalizeMaybe mt (thsRes sig)
  (arrName, domTy, codTy) <- matchBinaryCon mt classifierMode funTy
  guard (domTy == argTy)
  guard (codTy == resTy)
  pure arrName

inferAppBuiltinCandidate :: ModeTheory -> ModeName -> TmHeadSig -> Maybe (ObjName, Bool)
inferAppBuiltinCandidate mt classifierMode sig = do
  arrName <- inferAppBuiltinHead mt classifierMode sig
  etaCapable <- inferFunctionHeadEta (thsParams sig)
  pure (arrName, etaCapable)

defaultFunctionBuiltin :: FunctionBuiltin
defaultFunctionBuiltin =
  FunctionBuiltin
    { fbLamGen = GenName "lam"
    , fbAppGen = GenName "app"
    , fbArrTyCon = ObjName "Arr"
    , fbAllowEta = True
    }

functionBuiltins :: FunctionBuiltin -> BuiltinHeads
functionBuiltins fb =
  BuiltinHeads
    { bhFunctionSpace = Just fb
    , bhExtensionalHeads = M.empty
    , bhEliminators = M.empty
    , bhHeadRoles =
        M.fromList
          [ (fbLamGen fb, BuiltinExtensional)
          , (fbAppGen fb, BuiltinExtensional)
          ]
    }

extensionalBuiltins :: M.Map GenName ExtensionalBuiltin -> BuiltinHeads
extensionalBuiltins builtins =
  BuiltinHeads
    { bhFunctionSpace = Nothing
    , bhExtensionalHeads = builtins
    , bhEliminators = M.empty
    , bhHeadRoles = M.map (const BuiltinExtensional) builtins
    }

eliminatorBuiltins :: M.Map GenName EliminatorBuiltin -> BuiltinHeads
eliminatorBuiltins builtins =
  BuiltinHeads
    { bhFunctionSpace = Nothing
    , bhExtensionalHeads = M.empty
    , bhEliminators = builtins
    , bhHeadRoles = M.map (const BuiltinEliminator) builtins
    }

mergeBuiltinHeads :: BuiltinHeads -> BuiltinHeads -> Either Text BuiltinHeads
mergeBuiltinHeads left right = do
  functionSpace <-
    case (bhFunctionSpace left, bhFunctionSpace right) of
      (Just _, Just _) ->
        Left "validateDoctrine: internal error while merging duplicate function-space builtin metadata"
      (Just fb, Nothing) -> Right (Just fb)
      (Nothing, Just fb) -> Right (Just fb)
      (Nothing, Nothing) -> Right Nothing
  let overlappingRoles = M.keysSet (bhHeadRoles left) `S.intersection` M.keysSet (bhHeadRoles right)
  if S.null overlappingRoles
    then
      Right
        BuiltinHeads
          { bhFunctionSpace = functionSpace
          , bhExtensionalHeads = M.union (bhExtensionalHeads left) (bhExtensionalHeads right)
          , bhEliminators = M.union (bhEliminators left) (bhEliminators right)
          , bhHeadRoles = M.union (bhHeadRoles left) (bhHeadRoles right)
          }
    else
      Left
        ( "validateDoctrine: internal error while merging duplicate builtin-head roles ["
            <> T.intercalate ", " (map renderGenNameText (S.toList overlappingRoles))
            <> "]"
        )

inferFunctionBuiltinForMode
  :: Doctrine
  -> TypeTheory
  -> ModeName
  -> Either Text (Maybe FunctionBuiltin)
inferFunctionBuiltinForMode doc tt mode =
  case (M.null lamByArr, M.null appByArr) of
    (True, True) ->
      Right Nothing
    _ | not (null incompleteArrs) ->
        Left
          ( "validateDoctrine: mode "
              <> renderModeNameText mode
              <> " has incomplete function-space builtin evidence; missing counterpart for arrow constructor(s) ["
              <> T.intercalate ", " (map renderObjNameText incompleteArrs)
              <> "]; lambda candidates = {"
              <> renderCandidateMap lamByArr
              <> "}, application candidates = {"
              <> renderCandidateMap appByArr
              <> "}"
          )
    _ ->
      case completeArrs of
        [arr] ->
          let lams = M.findWithDefault [] arr lamByArr
              apps = M.findWithDefault [] arr appByArr
           in case (lams, apps) of
                ([(lamGen, lamEta)], [(appGen, appEta)]) ->
                  Right
                    ( Just
                        defaultFunctionBuiltin
                          { fbLamGen = lamGen
                          , fbAppGen = appGen
                          , fbArrTyCon = arr
                          , fbAllowEta = lamEta && appEta
                          }
                    )
                _ ->
                  Left
                    ( "validateDoctrine: mode "
                        <> renderModeNameText mode
                        <> " has ambiguous function-space builtin evidence for arrow constructor `"
                        <> renderObjNameText arr
                        <> "`; lambda candidates = ["
                        <> T.intercalate ", " (map (renderGenNameText . fst) lams)
                        <> "], application candidates = ["
                        <> T.intercalate ", " (map (renderGenNameText . fst) apps)
                        <> "]"
                    )
        [] ->
          Left
            ( "validateDoctrine: mode "
                <> renderModeNameText mode
                <> " has function-space builtin candidates, but no matching lambda/application pair was found"
            )
        _ ->
          Left
            ( "validateDoctrine: mode "
                <> renderModeNameText mode
                <> " has ambiguous function-space builtin evidence: multiple arrow constructors fit ["
                <> T.intercalate ", " (map renderObjNameText completeArrs)
                <> "]"
            )
  where
    mt = dModes doc
    classifierMode = modeClassifierMode mt mode
    headsInMode = M.toList (termHeadsForMode tt mode)

    lamCands :: [(ObjName, GenName, Bool)]
    lamCands =
      [ (arrName, g, etaCapable)
      | (g, sig) <- headsInMode
      , Just (arrName, etaCapable) <- [inferLamBuiltinCandidate mt classifierMode sig]
      ]

    appCands :: [(ObjName, GenName, Bool)]
    appCands =
      [ (arrName, g, etaCapable)
      | (g, sig) <- headsInMode
      , Just (arrName, etaCapable) <- [inferAppBuiltinCandidate mt classifierMode sig]
      ]

    lamByArr = M.fromListWith (<>) [ (arr, [(g, etaCapable)]) | (arr, g, etaCapable) <- lamCands ]
    appByArr = M.fromListWith (<>) [ (arr, [(g, etaCapable)]) | (arr, g, etaCapable) <- appCands ]

    allArrs = S.toList (M.keysSet lamByArr `S.union` M.keysSet appByArr)
    completeArrs =
      [ arr
      | arr <- allArrs
      , M.member arr lamByArr
      , M.member arr appByArr
      ]
    incompleteArrs =
      [ arr
      | arr <- allArrs
      , not (arr `elem` completeArrs)
      ]
    renderCandidateMap mp =
      T.intercalate
        "; "
        [ renderObjNameText arr <> " -> [" <> T.intercalate ", " (map (renderGenNameText . fst) gens) <> "]"
        | (arr, gens) <- M.toList mp
        ]

inferAndFinalizeFunctionBuiltins
  :: Bool
  -> Doctrine
  -> TypeTheory
  -> ModeName
  -> Either Text BuiltinHeads
inferAndFinalizeFunctionBuiltins requireCtorEligibility doc tt mode = do
  inferred <- inferFunctionBuiltinForMode doc tt mode
  case inferred of
    Nothing -> Right emptyBuiltinHeads
    Just fb -> finalizeFunctionBuiltinForMode requireCtorEligibility doc tt mode fb

finalizeFunctionBuiltinForMode
  :: Bool
  -> Doctrine
  -> TypeTheory
  -> ModeName
  -> FunctionBuiltin
  -> Either Text BuiltinHeads
finalizeFunctionBuiltinForMode requireCtorEligibility doc tt mode fb = do
  let mt = dModes doc
      classifierMode = modeClassifierMode mt mode
      arrName = fbArrTyCon fb
      arrGenName = GenName (renderObjNameText arrName)

  arrDecl <-
    case M.lookup classifierMode (dGens doc) >>= M.lookup arrGenName of
      Just gd -> Right gd
      Nothing ->
        Left
          ( "validateDoctrine: mode "
              <> renderModeNameText mode
              <> " is missing function-space arrow type constructor `"
              <> renderObjNameText arrName
              <> "` (no constructor-like generator `"
              <> renderModeNameText classifierMode
              <> "."
              <> renderObjNameText arrName
              <> "` declared)"
          )

  if isCtorLikeGen arrDecl
    then pure ()
    else
      Left
        ( "validateDoctrine: mode "
            <> renderModeNameText mode
            <> " requires function-space arrow type constructor `"
            <> renderObjNameText arrName
            <> "` to be constructor-like (no inputs)"
        )

  sig <- ctorSigFromGen arrDecl
  if length (csParams sig) == 2 && all isTyParam (csParams sig)
    then pure ()
    else
      Left
        ( "validateDoctrine: mode "
            <> renderModeNameText mode
            <> " requires function-space arrow type constructor `"
            <> renderObjNameText arrName
            <> "` to take exactly two type parameters"
        )

  if requireCtorEligibility
    then
      case M.lookup mode (ttCtorTablesByOwner tt) >>= M.lookup arrName of
        Just _ -> pure ()
        Nothing ->
          Left
            ( "validateDoctrine: mode "
                <> renderModeNameText mode
                <> " requires function-space arrow type constructor `"
                <> renderObjNameText arrName
                <> "` to be eligible for the mode (missing from derived constructor table)"
            )
    else
      pure ()

  pure (functionBuiltins fb)
  where
    isTyParam param =
      case param of
        GP_Ty _ -> True
        GP_Tm _ -> False

inferTransportBuiltinCandidate
  :: TypeTheory
  -> TmHeadSig
  -> Either Text Bool
inferTransportBuiltinCandidate tt sig =
  case (thsInputs sig, thsBinders sig) of
    ([inputSort], []) ->
      if inputSort == thsRes sig
        then Right False
        else
          defEqObj tt tmCtx inputSort (thsRes sig)
    _ ->
      Right False
  where
    tmCtx =
      [ tmvSort v
      | GP_Tm v <- thsParams sig
      ]

builtinElimExplicitDeclHint :: Text
builtinElimExplicitDeclHint =
  " Add an explicit `builtin eliminator ...` declaration if this head is intended to use builtin eliminator semantics."

computationalCellPairs :: Cell2 -> [(Diagram, Diagram)]
computationalCellPairs cell =
  case c2Orient cell of
    LR -> [(c2LHS cell, c2RHS cell)]
    RL -> [(c2RHS cell, c2LHS cell)]
    Bidirectional -> [(c2LHS cell, c2RHS cell), (c2RHS cell, c2LHS cell)]
    Unoriented -> []

data CtorCaseEvidence = CtorCaseEvidence
  { cceScrutineeIndex :: Int
  , cceHeadArgs :: [CodeArg]
  , cceCtorGen :: GenName
  , cceBinderIndex :: Maybe Int
  , cceBranchInputHints :: Maybe [BranchInputSource]
  }

cellHeadConstructorCasesForMode
  :: Doctrine
  -> TypeTheory
  -> ModeName
  -> Either Text (M.Map GenName [CtorCaseEvidence])
cellHeadConstructorCasesForMode doc tt mode =
  foldM step M.empty (filter ((== Computational) . c2Class) (dCells2 doc))
  where
    heads = termHeadsForMode tt mode

    step acc cell =
      foldM
        (stepOne cell)
        acc
        (computationalCellPairs cell)

    stepOne cell acc (lhs, rhs)
      | dMode lhs /= mode =
          Right acc
      | otherwise =
          case cellHeadConstructorCase tt heads (c2TmVars cell) lhs rhs of
            Left _ ->
              Right acc
            Right Nothing ->
              Right acc
            Right (Just (g, evidence)) ->
              Right (M.insertWith (flip (<>)) g [evidence] acc)

cellHeadConstructorCase
  :: TypeTheory
  -> M.Map GenName TmHeadSig
  -> [TmVar]
  -> Diagram
  -> Diagram
  -> Either Text (Maybe (GenName, CtorCaseEvidence))
cellHeadConstructorCase tt heads _tmVars diag rhs =
  case dOut diag of
    [outPid] ->
      case producerEdge diag outPid of
        Nothing ->
          pure Nothing
        Just rootEdge ->
          case ePayload rootEdge of
            PGen g args bargs
              | not (null bargs)
              , Just sig <- M.lookup g heads
              , length args == length (thsParams sig)
              , length (eIns rootEdge) == length (thsInputs sig)
              , length bargs == length (thsBinders sig)
              , length (eOuts rootEdge) == 1 ->
                  case constructorInput (zip [0 :: Int ..] (eIns rootEdge)) of
                    Just (scrutineeIx, ctor, ctorEdge) -> do
                      let holeToBinderIndex =
                            M.fromList
                              [ (hole, i)
                              | (i, barg) <- zip [0 :: Int ..] bargs
                              , BAMeta hole <- [barg]
                              ]
                          boundaryHints = boundarySourceHints rootEdge ctorEdge scrutineeIx
                          (binderIndex, branchInputHints) =
                            case rhsSpliceEvidence tt rhs boundaryHints of
                              Just (hole, hints) ->
                                (M.lookup hole holeToBinderIndex, Just hints)
                              Nothing ->
                                (Nothing, Nothing)
                      pure $
                        Just
                          ( g
                          , CtorCaseEvidence
                              { cceScrutineeIndex = scrutineeIx
                              , cceHeadArgs = args
                              , cceCtorGen = ctor
                              , cceBinderIndex = binderIndex
                              , cceBranchInputHints = branchInputHints
                              }
                          )
                    Nothing ->
                      pure Nothing
            _ ->
              pure Nothing
    _ ->
      pure Nothing
  where
    constructorInput =
      listToMaybe . mapMaybe one
      where
        one (i, pid) = do
          scrutineeEdge <- producerEdge diag pid
          case ePayload scrutineeEdge of
            PGen ctor _ ctorBargs
              | null ctorBargs
              , eOuts scrutineeEdge == [pid] ->
                  Just (i, ctor, scrutineeEdge)
            _ ->
              Nothing

    boundarySourceHints rootEdge ctorEdge scrutineeIx =
      let boundaryLocals = M.fromList (zip (dIn diag) [0 :: Int ..])
          outerHints =
            M.fromList
              [ (localIx, BISOuterInput i)
              | (i, pid) <- zip [0 :: Int ..] (eIns rootEdge)
              , i /= scrutineeIx
              , Just localIx <- [M.lookup pid boundaryLocals]
              ]
          ctorHints =
            M.fromList
              [ (localIx, BISCtorField i)
              | (i, pid) <- zip [0 :: Int ..] (eIns ctorEdge)
              , Just localIx <- [M.lookup pid boundaryLocals]
              ]
       in M.union outerHints ctorHints

    rhsSpliceEvidence tt0 rhs0 boundaryHints = do
      boundarySorts <- either (const Nothing) Just (mapM (\pid -> requirePortType "validateDoctrine: builtin rhs evidence" rhs0 pid) (dIn rhs0))
      expectedSort <- either (const Nothing) Just (termDiagramOutputSort "validateDoctrine: builtin rhs evidence" rhs0)
      expr <- either (const Nothing) Just (diagramGraphToRuleExpr tt0 boundarySorts expectedSort rhs0)
      case expr of
        TMSplice hole _ args ->
          let hints = mapM (directBoundarySource boundaryHints) args
           in fmap (\hs -> (hole, hs)) hints
        _ ->
          Nothing

    directBoundarySource boundaryHints tm =
      case tm of
        TMBound i ->
          M.lookup i boundaryHints
        _ ->
          Nothing

    producerEdge d pid = do
      eid <- IM.lookup (unPortId pid) (dProd d)
      edgeId <- eid
      IM.lookup (unEdgeId edgeId) (dEdges d)

matchHeadSubst
  :: TypeTheory
  -> [GenParam]
  -> Obj
  -> Obj
  -> Either Text (Maybe (M.Map TmVar CodeArg))
matchHeadSubst tt params pat target = do
  subst <-
    case unifyObjFlex tt [] flex emptySubst pat target of
      Left _ ->
        pure Nothing
      Right subst0 ->
        Just <$> normalizeSubst tt subst0
  pure
    ( fmap
        (\subst0 -> M.fromList (map (\(v, obj) -> (v, CAObj obj)) (codeBindings subst0) <> map (\(v, tm) -> (v, CATm tm)) (tmBindings subst0)))
        subst
    )
  where
    flex =
      S.fromList
        [ v
        | param <- params
        , v <-
            case param of
              GP_Ty v' -> [v']
              GP_Tm v' -> [v']
        ]

instantiateTypeHeadObj
  :: TypeTheory
  -> M.Map TmVar CodeArg
  -> Obj
  -> Either Text Obj
instantiateTypeHeadObj tt subst obj = do
  obj' <- applyHeadSubstObj tt (structuralConvEnv tt) [] subst obj
  normalizeObjDeep tt obj'

instantiateHeadStoredSubst
  :: TypeTheory
  -> TmHeadSig
  -> [CodeArg]
  -> Either Text (M.Map TmVar CodeArg)
instantiateHeadStoredSubst tt sig args =
  instantiateStoredHeadSubst tt [] sig args

instantiateBuiltinEvidenceBinderSig
  :: TypeTheory
  -> M.Map TmVar CodeArg
  -> BinderSig
  -> Either Text BinderSig
instantiateBuiltinEvidenceBinderSig tt headSubst slot = do
  slot' <- instantiateStructuralBinderSig tt [] headSubst slot
  let tmCtx0 = bsTmCtx slot'
  tmCtx <- mapM (normalizeObjDeep tt) tmCtx0
  let dom0 = bsDom slot'
  dom <- mapM (normalizeObjDeepWithCtx tt tmCtx) dom0
  let cod0 = bsCod slot'
  cod <- mapM (normalizeObjDeepWithCtx tt tmCtx) cod0
  pure
    slot'
      { bsTmCtx = tmCtx
      , bsDom = dom
      , bsCod = cod
      }

directParamIndex :: [GenParam] -> CodeArg -> Maybe Int
directParamIndex params arg =
  fst <$> L.find (matchesParam . snd) (zip [0 :: Int ..] params)
  where
    matchesParam param =
      case (param, arg) of
        (GP_Ty v, CAObj (OVar v')) ->
          sameTmVarId v v'
        (GP_Tm v, CATm tm) ->
          termMetaOnly tm == Just v
        _ ->
          False

    termMetaOnly (TermDiagram diag) =
      case (IM.elems (dEdges diag), dIn diag, dOut diag) of
        ([edge], [], [outBoundary]) ->
          case (ePayload edge, eIns edge, eOuts edge) of
            (PTmMeta v, [], [outPid]) | outPid == outBoundary -> Just v
            _ -> Nothing
        _ -> Nothing

scrutineeFamilyShape
  :: TmHeadSig
  -> Int
  -> Maybe (ObjRef, M.Map Int Int)
scrutineeFamilyShape sig scrutineeIx = do
  scrutTy <- safeNth (thsInputs sig) scrutineeIx
  case objCode scrutTy of
    CTCon ref args ->
      let headParamByFamilyArg =
            M.fromList
              [ (paramIx, familyArgIx)
              | (familyArgIx, arg) <- zip [0 :: Int ..] args
              , Just paramIx <- [directParamIndex (thsParams sig) arg]
              ]
       in Just (ref, headParamByFamilyArg)
    _ ->
      Nothing
  where
    safeNth xs i
      | i < 0 =
          Nothing
      | otherwise =
          case drop i xs of
            (x:_) -> Just x
            [] -> Nothing

recursiveCallSourcesForInput
  :: [GenParam]
  -> ObjRef
  -> M.Map Int Int
  -> [GenParam]
  -> Obj
  -> Maybe [RecursiveHeadArgSource]
recursiveCallSourcesForInput headParams scrutineeRef headParamByFamilyArg ctorParams inputSort =
  case objCode inputSort of
    CTCon ref _
      | ref == scrutineeRef ->
          mapM sourceForHeadParam (zip [0 :: Int ..] headParams)
    _ ->
      Nothing
  where
    sourceForHeadParam (headParamIx, _headParam) =
      case M.lookup headParamIx headParamByFamilyArg of
        Nothing ->
          Just (RHOuterHeadArg headParamIx)
        Just familyArgIx -> do
          familyArg <- safeNth args familyArgIx
          case directParamIndex ctorParams familyArg of
            Just ctorParamIx ->
              Just (RHCtorArg ctorParamIx)
            Nothing ->
              RHOuterHeadArg <$> directParamIndex headParams familyArg

    args =
      case objCode inputSort of
        CTCon _ args0 -> args0
        _ -> []

    safeNth xs i
      | i < 0 =
          Nothing
      | otherwise =
          case drop i xs of
            (x:_) -> Just x
            [] -> Nothing

data TmBranchSource = TmBranchSource
  { tbsSource :: BranchInputSource
  , tbsTerm :: TermDiagram
  , tbsSort :: Obj
  }

inferTmCtxSources
  :: TypeTheory
  -> [TmBranchSource]
  -> [Obj]
  -> Either Text (Maybe ([BranchInputSource], M.Map Int TermDiagram))
inferTmCtxSources tt available wantSorts =
  go 0 [] M.empty available wantSorts
  where
    convEnv = structuralConvEnv tt

    go _ acc subst _ [] =
      pure (Just (reverse acc, subst))
    go localIx acc subst remaining (wantSort0 : rest) = do
      wantSort1 <- instantiateHostBoundObj tt convEnv [] subst wantSort0
      wantSort <- normalizeObjDeep tt wantSort1
      case break (\source -> tbsSort source == wantSort) remaining of
        (before, match : after) ->
          go
            (localIx + 1)
            (tbsSource match : acc)
            (M.insert localIx (tbsTerm match) subst)
            (before <> after)
            rest
        (_, []) ->
          pure Nothing

instantiateLocalTmSort
  :: TypeTheory
  -> M.Map Int TermDiagram
  -> Obj
  -> Either Text Obj
instantiateLocalTmSort tt localSubst sortTy0 = do
  sortTy1 <- instantiateHostBoundObj tt (structuralConvEnv tt) [] localSubst sortTy0
  normalizeObjDeep tt sortTy1

inferBranchSourcesBySort
  :: [(BranchInputSource, Obj)]
  -> [Obj]
  -> [BranchInputSource]
inferBranchSourcesBySort available wantSorts =
  go available slotDom
  where
    slotDom = wantSorts

    go _ [] = []
    go remaining (wantSort : rest) =
      case break (\(_, sourceSort) -> sourceSort == wantSort) remaining of
        (before, match : after) ->
          fst match : go (before <> after) rest
        (_, []) ->
          []

inferPlainBranchSources
  :: [(Int, Obj)]
  -> [Obj]
  -> M.Map Int [RecursiveHeadArgSource]
  -> Obj
  -> [(BranchInputSource, Obj)]
inferPlainBranchSources outerInputSorts inputSorts recursiveCalls resTy =
  [ (BISOuterInput i, sortTy)
  | (i, sortTy) <- outerInputSorts
  ]
    <> concat
      [ (BISCtorField i, sortTy) :
          [ (BISRecursiveResult i sources, resTy)
          | Just sources <- [M.lookup i recursiveCalls]
          ]
      | (i, sortTy) <- zip [0 :: Int ..] inputSorts
      ]

inferElimBranchBuiltin
  :: TypeTheory
  -> ModeName
  -> [GenParam]
  -> [TmBranchSource]
  -> [Obj]
  -> Maybe [BranchInputSource]
  -> ObjRef
  -> M.Map Int Int
  -> Obj
  -> Obj
  -> GenName
  -> BinderSig
  -> Either Text (Maybe ElimBranchBuiltin)
inferElimBranchBuiltin tt mode headParams outerHeadTmTerms outerInputSorts branchInputHints scrutineeRef headParamByFamilyArg scrutTyNorm resTyNorm ctorGen slot0 = do
  case lookupTmHeadSig tt mode ctorGen of
    Nothing ->
      pure Nothing
    Just sig
      | not (null (thsBinders sig)) ->
          pure Nothing
      | otherwise -> do
          mSubst <- matchHeadSubst tt (thsParams sig) (thsRes sig) scrutTyNorm
          case mSubst of
            Nothing ->
              pure Nothing
            Just subst -> do
              inputSorts0 <- mapM (instantiateTypeHeadObj tt subst) (thsInputs sig)
              inputSorts <- mapM (normalizeObjDeep tt) inputSorts0
              ctorHeadTmTerms <- instantiateTermParamTerms BISCtorHeadTmParam (thsParams sig) subst
              recursiveCalls <- collectRecursiveCalls sig
              slotTmCtx <- mapM (normalizeObjDeep tt) (bsTmCtx slot0)
              tmCtxMatch <- inferTmCtxSources tt (outerHeadTmTerms <> ctorHeadTmTerms) slotTmCtx
              case tmCtxMatch of
                Nothing ->
                  pure Nothing
                Just (tmCtxInputs, localTmSubst) -> do
                  slotDom <- mapM (instantiateLocalTmSort tt localTmSubst) (bsDom slot0)
                  slotCod <- mapM (instantiateLocalTmSort tt localTmSubst) (bsCod slot0)
                  let plainSources = inferPlainBranchSources (zip [0 :: Int ..] outerInputSorts) inputSorts recursiveCalls resTyNorm
                  hintedInputs <-
                    case branchInputHints of
                      Nothing ->
                        Right Nothing
                      Just hints ->
                        resolveBranchInputHints ctorGen plainSources slotDom hints
                  let branchInputs =
                        case hintedInputs of
                          Just hints -> hints
                          Nothing -> inferBranchSourcesBySort plainSources slotDom
                  if slotCod == [resTyNorm]
                       && length branchInputs == length slotDom
                    then
                      pure
                        ( Just
                            ElimBranchBuiltin
                              { ebbCtorGen = ctorGen
                              , ebbTmCtxInputs = tmCtxInputs
                              , ebbInputs = branchInputs
                              }
                        )
                    else
                      pure Nothing
  where
    instantiateTermParamTerms mkSource params subst =
      fmap catMaybes $
        forM
          (zip [0 :: Int ..] params)
          ( \(i, param) ->
              case param of
                GP_Ty _ ->
                  pure Nothing
                GP_Tm v -> do
                  sortTy0 <- applyHeadSubstObj tt (structuralConvEnv tt) [] subst (tmvSort v)
                  sortTy <- normalizeObjDeep tt sortTy0
                  case M.lookup v subst of
                    Just (CATm tm) ->
                      pure
                        ( Just
                            TmBranchSource
                              { tbsSource = mkSource i
                              , tbsTerm = tm
                              , tbsSort = sortTy
                              }
                        )
                    Just (CAObj _) ->
                      Left "validateDoctrine: builtin branch inference expected a term-valued generator parameter substitution"
                    Nothing ->
                      pure Nothing
          )

    collectRecursiveCalls ctorSig =
      pure
        ( M.fromList
            [ (i, sources)
            | (i, inputSort0) <- zip [0 :: Int ..] (thsInputs ctorSig)
            , Just sources <-
                [ recursiveCallSourcesForInput
                    headParams
                    scrutineeRef
                    headParamByFamilyArg
                    (thsParams ctorSig)
                    inputSort0
                ]
            ]
        )

    resolveBranchInputHints ctor plainSources slotDom hints
      | length hints /= length slotDom =
          Left
            ( "validateDoctrine: builtin branch inference extracted "
                <> T.pack (show (length hints))
                <> " rhs splice inputs for constructor "
                <> renderGenNameText ctor
                <> " but the branch binder expects "
                <> T.pack (show (length slotDom))
                <> " inputs"
                <> builtinElimExplicitDeclHint
            )
      | and
          [ maybe False (== wantSort) (lookup hint plainSources)
          | (hint, wantSort) <- zip hints slotDom
          ] =
          Right (Just hints)
      | otherwise =
          Left
            ( "validateDoctrine: builtin branch inference extracted rhs splice inputs for constructor "
                <> renderGenNameText ctor
                <> " that do not match the inferred branch binder input sorts"
                <> builtinElimExplicitDeclHint
            )

inferInductiveElimBuiltinCandidate
  :: TypeTheory
  -> ModeName
  -> Int
  -> TmHeadSig
  -> [CtorCaseEvidence]
  -> Either Text (Maybe InductiveElimBuiltin)
inferInductiveElimBuiltinCandidate tt mode scrutineeIx sig ctorCases
  | null (thsBinders sig) =
      Right Nothing
  | otherwise = do
      case scrutineeFamilyShape sig scrutineeIx of
        Nothing ->
          Right Nothing
        Just (scrutineeRef, headParamByFamilyArg) -> do
          orderedCases <- assignCasesToBinders ctorCases (thsBinders sig)
          cases <- mapM (inferOneCase scrutineeRef headParamByFamilyArg) orderedCases
          pure $
            case orderedCases of
              [] ->
                Nothing
              _ ->
                case sequence cases of
                  Just builtinCases ->
                    Just
                      InductiveElimBuiltin
                        { iebScrutineeIndex = scrutineeIx
                        , iebScrutineeTyCon = scrutineeRef
                        , iebBranches = builtinCases
                        }
                  Nothing ->
                    Nothing
  where
    assignCasesToBinders cases slots =
      let slotCount = length slots
          explicit =
            [ (ix, evidence)
            | evidence <- cases
            , Just ix <- [cceBinderIndex evidence]
            ]
          explicitIndices = map fst explicit
          uniqueExplicit = length (S.fromList explicitIndices) == length explicitIndices
          inRange = all (\ix -> ix >= 0 && ix < slotCount) explicitIndices
       in if not uniqueExplicit
            then
              Left
                ("validateDoctrine: builtin eliminator inference found conflicting rhs splice-hole evidence for binder-slot assignment"
                  <> builtinElimExplicitDeclHint
                )
            else
              if not inRange
                then
                  Left
                    ("validateDoctrine: builtin eliminator inference found out-of-range rhs splice-hole evidence for binder-slot assignment"
                      <> builtinElimExplicitDeclHint
                    )
                else
                  if length cases /= slotCount
                    then Right []
                    else
                      case explicit of
                        []
                          | length cases == slotCount ->
                              Right (zip cases slots)
                        _ ->
                          let complete = length explicit == slotCount
                              explicitMap = M.fromList explicit
                           in if complete
                                then Right [ (explicitMap M.! ix, slot) | (ix, slot) <- zip [0 :: Int ..] slots ]
                                else Right (zip cases slots)

    inferOneCase scrutineeRef headParamByFamilyArg (evidence, slot0) = do
      let headArgs = cceHeadArgs evidence
          ctorGen = cceCtorGen evidence
          branchInputHints = cceBranchInputHints evidence
      headSubst <- instantiateHeadStoredSubst tt sig headArgs
      scrutTy0 <-
        case safeNth (thsInputs sig) scrutineeIx of
          Just scrutTy -> Right scrutTy
          Nothing -> Left "validateDoctrine: builtin inference saw an out-of-bounds scrutinee index"
      scrutTyNorm <- instantiateTypeHeadObj tt headSubst scrutTy0
      outerHeadTmTerms <- instantiateTermParamTerms BISOuterHeadTmParam (thsParams sig) headSubst
      outerInputSorts0 <- mapM (instantiateTypeHeadObj tt headSubst) (thsInputs sig)
      outerInputSorts <- mapM (normalizeObjDeep tt) outerInputSorts0
      resTy0 <- applyHeadSubstObj tt (structuralConvEnv tt) [] headSubst (thsRes sig)
      resTyNorm <- normalizeObjDeep tt resTy0
      slot <- instantiateBuiltinEvidenceBinderSig tt headSubst slot0
      inferElimBranchBuiltin tt mode (thsParams sig) outerHeadTmTerms outerInputSorts branchInputHints scrutineeRef headParamByFamilyArg scrutTyNorm resTyNorm ctorGen slot

    safeNth xs i
      | i < 0 =
          Nothing
      | otherwise =
          case drop i xs of
            (x:_) -> Just x
            [] -> Nothing

    instantiateTermParamTerms mkSource params subst =
      fmap catMaybes $
        forM
          (zip [0 :: Int ..] params)
          ( \(i, param) ->
              case param of
                GP_Ty _ ->
                  pure Nothing
                GP_Tm v -> do
                  sortTy0 <- applyHeadSubstObj tt (structuralConvEnv tt) [] subst (tmvSort v)
                  sortTy <- normalizeObjDeep tt sortTy0
                  case M.lookup v subst of
                    Just (CATm tm) ->
                      pure
                        ( Just
                            TmBranchSource
                              { tbsSource = mkSource i
                              , tbsTerm = tm
                              , tbsSort = sortTy
                              }
                        )
                    Just (CAObj _) ->
                      Left "validateDoctrine: builtin eliminator inference expected a term-valued parameter substitution"
                    Nothing ->
                      pure Nothing
          )

data ExplicitBranchSourceValue = ExplicitBranchSourceValue
  { ebsvSort :: Obj
  , ebsvTerm :: TermDiagram
  }

nthMaybe :: [a] -> Int -> Maybe a
nthMaybe xs i
  | i < 0 =
      Nothing
  | otherwise =
      case drop i xs of
        (x:_) -> Just x
        [] -> Nothing

mkSymbolicMetaTermDiagram
  :: Obj
  -> TmVar
  -> Either Text TermDiagram
mkSymbolicMetaTermDiagram sortTy v = do
  let ownerMode = objOwnerMode sortTy
      v' = v { tmvSort = sortTy }
  let (outPid, d0) = freshPort sortTy (emptyDiagram ownerMode [])
  d1 <- addEdgePayload (PTmMeta v') [] [outPid] d0
  let d2 = d1 { dOut = [outPid] }
  validateDiagram d2
  pure (TermDiagram d2)

mkBoundarySourceTermDiagram
  :: TypeTheory
  -> [Obj]
  -> Obj
  -> Int
  -> Either Text TermDiagram
mkBoundarySourceTermDiagram tt tmCtx sortTy ix =
  termExprToDiagramChecked tt tmCtx sortTy (TMBound ix)

mkSelfHeadCodeArgs
  :: TypeTheory
  -> [GenParam]
  -> Either Text [CodeArg]
mkSelfHeadCodeArgs tt =
  mapM mkOne
  where
    mkOne param =
      case param of
        GP_Ty v ->
          Right (CAObj (OVar v))
        GP_Tm v -> do
          sortTy <- normalizeObjDeep tt (tmvSort v)
          CATm <$> mkSymbolicMetaTermDiagram sortTy v

completeCtorParamSubst
  :: TypeTheory
  -> [GenParam]
  -> M.Map TmVar CodeArg
  -> Either Text (M.Map TmVar CodeArg)
completeCtorParamSubst tt params matched =
  foldM step matched params
  where
    step subst param =
      case param of
        GP_Ty v ->
          pure (M.insertWith (\_ old -> old) v (CAObj (OVar v)) subst)
        GP_Tm v -> do
          sortTy <- normalizeObjDeep tt (tmvSort v)
          tm <- mkSymbolicMetaTermDiagram sortTy v
          pure (M.insertWith (\_ old -> old) v (CATm tm) subst)

explicitBranchSourceValues
  :: TypeTheory
  -> TmHeadSig
  -> Int
  -> ObjRef
  -> M.Map Int Int
  -> TmHeadSig
  -> Either Text (M.Map BranchInputSource ExplicitBranchSourceValue, [Obj], Obj)
explicitBranchSourceValues tt sig scrutineeIx scrutineeRef headParamByFamilyArg ctorSig = do
  scrutTy0 <-
    case nthMaybe (thsInputs sig) scrutineeIx of
      Just scrutTy -> Right scrutTy
      Nothing -> Left "validateDoctrine: explicit builtin eliminator scrutinee index is out of bounds"
  scrutTyNorm <- normalizeObjDeep tt scrutTy0
  matchedCtorSubst <-
    matchHeadSubst tt (thsParams ctorSig) (thsRes ctorSig) scrutTyNorm >>= \mSubst ->
      case mSubst of
        Nothing ->
          Left "validateDoctrine: explicit builtin eliminator branch constructor does not match the scrutinee family"
        Just subst ->
          Right subst
  ctorSubst <- completeCtorParamSubst tt (thsParams ctorSig) matchedCtorSubst
  selfHeadArgs <- mkSelfHeadCodeArgs tt (thsParams sig)
  ctorHeadArgs <-
    forM
      (thsParams ctorSig)
      ( \param ->
          case param of
            GP_Ty v ->
              case M.lookup v ctorSubst of
                Just arg -> Right arg
                Nothing -> Left "validateDoctrine: internal error completing constructor type-parameter substitution"
            GP_Tm v ->
              case M.lookup v ctorSubst of
                Just arg -> Right arg
                Nothing -> Left "validateDoctrine: internal error completing constructor term-parameter substitution"
      )
  outerHeadValues <- fmap catMaybes $
    forM
      (zip [0 :: Int ..] (thsParams sig))
      ( \(i, param) ->
          case param of
            GP_Ty _ ->
              pure Nothing
            GP_Tm v -> do
              sortTy <- normalizeObjDeep tt (tmvSort v)
              tm <- mkSymbolicMetaTermDiagram sortTy v
              pure (Just (BISOuterHeadTmParam i, ExplicitBranchSourceValue sortTy tm))
      )
  outerInputSorts <- mapM (normalizeObjDeep tt) (thsInputs sig)
  ctorHeadValues <- fmap catMaybes $
    forM
      (zip [0 :: Int ..] (thsParams ctorSig))
      ( \(i, param) ->
          case param of
            GP_Ty _ ->
              pure Nothing
            GP_Tm v -> do
              sortTy0 <- applyHeadSubstObj tt (structuralConvEnv tt) [] ctorSubst (tmvSort v)
              sortTy <- normalizeObjDeep tt sortTy0
              tm <-
                case M.lookup v ctorSubst of
                  Just (CATm tm0) -> Right tm0
                  Just (CAObj _) -> Left "validateDoctrine: explicit builtin eliminator constructor term parameter instantiated to a type"
                  Nothing -> Left "validateDoctrine: internal error missing completed constructor term parameter substitution"
              pure (Just (BISCtorHeadTmParam i, ExplicitBranchSourceValue sortTy tm))
      )
  ctorInputSorts <- mapM (instantiateTypeHeadObj tt ctorSubst) (thsInputs ctorSig)
  resTyNorm <- normalizeObjDeep tt (thsRes sig)
  let recursiveCalls =
        M.fromList
          [ (i, sources)
          | (i, inputSort0) <- zip [0 :: Int ..] (thsInputs ctorSig)
          , Just sources <-
              [ recursiveCallSourcesForInput
                  (thsParams sig)
                  scrutineeRef
                  headParamByFamilyArg
                  (thsParams ctorSig)
                  inputSort0
              ]
          ]
  recursiveValues <-
    forM
      (M.toAscList recursiveCalls)
      ( \(i, sources) -> do
          nextHeadArgs <- mapM (recursiveSourceCodeArg selfHeadArgs ctorHeadArgs) sources
          nextHeadSubst <- instantiateStoredHeadSubst tt [] sig nextHeadArgs
          nextRes0 <- applyHeadSubstObj tt (structuralConvEnv tt) [] nextHeadSubst (thsRes sig)
          nextRes <- normalizeObjDeep tt nextRes0
          pure (BISRecursiveResult i sources, nextRes)
      )
  let boundarySourceSorts =
        [ (BISOuterInput i, sortTy)
        | (i, sortTy) <- zip [0 :: Int ..] outerInputSorts
        ]
          <> [ (BISCtorField i, sortTy)
             | (i, sortTy) <- zip [0 :: Int ..] ctorInputSorts
             ]
          <> recursiveValues
      ambientTmCtx = map snd boundarySourceSorts
  boundaryValues <-
    fmap M.fromList $
      forM
        (zip [0 :: Int ..] boundarySourceSorts)
        ( \(ix, (source, sortTy)) -> do
            tm <- mkBoundarySourceTermDiagram tt ambientTmCtx sortTy ix
            pure (source, ExplicitBranchSourceValue sortTy tm)
        )
  pure (M.unions [M.fromList outerHeadValues, M.fromList ctorHeadValues, boundaryValues], ambientTmCtx, resTyNorm)
  where
    recursiveSourceCodeArg selfHeadArgs ctorHeadArgs source =
      case source of
        RHOuterHeadArg i ->
          case nthMaybe selfHeadArgs i of
            Just arg -> Right arg
            Nothing -> Left "validateDoctrine: explicit builtin eliminator recursive_result refers to a missing outer head argument"
        RHCtorArg i ->
          case nthMaybe ctorHeadArgs i of
            Just arg -> Right arg
            Nothing -> Left "validateDoctrine: explicit builtin eliminator recursive_result refers to a missing constructor head argument"

validateExplicitBranchSelection
  :: TypeTheory
  -> TmHeadSig
  -> Int
  -> ObjRef
  -> M.Map Int Int
  -> TmHeadSig
  -> BuiltinBranchDecl
  -> BinderSig
  -> Either Text ()
validateExplicitBranchSelection tt sig scrutineeIx scrutineeRef headParamByFamilyArg ctorSig branchDecl slot0 = do
  (sourceValues, ambientTmCtx, resTyNorm) <- explicitBranchSourceValues tt sig scrutineeIx scrutineeRef headParamByFamilyArg ctorSig
  (slotTmCtx, localTmSubst) <- validateLocalTmCtxSources sourceValues ambientTmCtx
  dom0 <- instantiateHostBoundCtx tt (structuralConvEnv tt) ambientTmCtx localTmSubst (bsDom slot0)
  dom <- normalizeCtxStructurallyWithPrefix tt (structuralConvEnv tt) slotTmCtx dom0
  validatePlainSources "input" sourceValues ambientTmCtx (bbdInputs branchDecl) dom
  cod0 <- instantiateHostBoundCtx tt (structuralConvEnv tt) ambientTmCtx localTmSubst (bsCod slot0)
  cod <- normalizeCtxStructurallyWithPrefix tt (structuralConvEnv tt) slotTmCtx cod0
  case cod of
    [codTy] -> do
      ok <- defEqObj tt ambientTmCtx codTy resTyNorm
      if ok
        then Right ()
        else
          Left
            ( "validateDoctrine: explicit builtin eliminator branch "
                <> renderGenNameText (bbdCtor branchDecl)
                <> " returns the wrong result sort"
            )
    _ ->
      Left
        ( "validateDoctrine: explicit builtin eliminator branch "
            <> renderGenNameText (bbdCtor branchDecl)
            <> " binder codomain must be exactly one result term"
        )
  where
    validateLocalTmCtxSources sourceValues ambientTmCtx =
      go 0 [] M.empty (bsTmCtx slot0) (bbdTmCtxInputs branchDecl)
      where
        go _ acc subst [] [] =
          pure (reverse acc, subst)
        go ix acc subst (expected0 : expectedRest) (source : sourceRest) = do
          sourceVal <- requireSource sourceValues source
          expected1 <- instantiateHostBoundObj tt (structuralConvEnv tt) ambientTmCtx subst expected0
          expected <- normalizeObjDeepWithCtx tt ambientTmCtx expected1
          ok <- defEqObj tt ambientTmCtx (ebsvSort sourceVal) expected
          if ok
            then Right ()
            else
              Left
                ( "validateDoctrine: explicit builtin eliminator branch "
                    <> renderGenNameText (bbdCtor branchDecl)
                    <> " local tm-context source sort mismatch at index "
                    <> T.pack (show ix)
                )
          go (ix + 1) (expected : acc) (M.insert ix (ebsvTerm sourceVal) subst) expectedRest sourceRest
        go _ _ _ _ _ =
          Left "validateDoctrine: explicit builtin eliminator branch local tm-context arity mismatch"

    validatePlainSources label sourceValues ambientTmCtx sources expectedSorts =
      sequence_
        [ do
            sourceVal <- requireSource sourceValues source
            ok <- defEqObj tt ambientTmCtx (ebsvSort sourceVal) expected
            if ok
              then Right ()
              else
                Left
                  ( "validateDoctrine: explicit builtin eliminator branch "
                      <> renderGenNameText (bbdCtor branchDecl)
                      <> " "
                      <> label
                      <> " source sort mismatch at index "
                      <> T.pack (show ix)
                  )
        | (ix, (source, expected)) <- zip [0 :: Int ..] (zip sources expectedSorts)
        ]

    requireSource sourceValues source =
      case M.lookup source sourceValues of
        Just one -> Right one
        Nothing ->
          Left "validateDoctrine: internal error resolving explicit builtin branch source"

explicitBuiltinDeclsForMode :: Doctrine -> ModeName -> [BuiltinDecl]
explicitBuiltinDeclsForMode doc mode =
  [ decl
  | decl <- dBuiltins doc
  , bdMode decl == mode
  ]

explicitExtensionalHeadSetForMode :: Doctrine -> ModeName -> S.Set GenName
explicitExtensionalHeadSetForMode doc mode =
  S.fromList
    [ bdHead decl
    | decl <- explicitBuiltinDeclsForMode doc mode
    , case bdSpec decl of
        BDTransport -> True
        BDInductiveElim _ _ -> False
    ]

explicitEliminatorHeadSetForMode :: Doctrine -> ModeName -> S.Set GenName
explicitEliminatorHeadSetForMode doc mode =
  S.fromList
    [ bdHead decl
    | decl <- explicitBuiltinDeclsForMode doc mode
    , case bdSpec decl of
        BDTransport -> False
        BDInductiveElim _ _ -> True
    ]

compileExplicitTransportBuiltinsForMode
  :: Doctrine
  -> TypeTheory
  -> ModeName
  -> Either Text BuiltinHeads
compileExplicitTransportBuiltinsForMode doc tt mode = do
  builtins <- fmap M.fromList (mapM compileOne decls)
  pure (extensionalBuiltins builtins)
  where
    decls =
      [ decl
      | decl <- explicitBuiltinDeclsForMode doc mode
      , case bdSpec decl of
          BDTransport -> True
          BDInductiveElim _ _ -> False
      ]

    compileOne decl = do
      sig <-
        case lookupTmHeadSig tt mode (bdHead decl) of
          Nothing ->
            Left
              ( "validateDoctrine: explicit builtin transport references unknown term head "
                  <> renderModeNameText mode
                  <> "."
                  <> renderGenNameText (bdHead decl)
              )
          Just sig -> Right sig
      isTransport <- inferTransportBuiltinCandidate tt sig
      if isTransport
        then pure (bdHead decl, BuiltinTransport)
        else
          Left
            ( "validateDoctrine: explicit builtin transport head "
                <> renderModeNameText mode
                <> "."
                <> renderGenNameText (bdHead decl)
                <> " does not match the transport builtin shape"
            )

compileExplicitEliminatorBuiltinsForMode
  :: Doctrine
  -> TypeTheory
  -> ModeName
  -> Either Text BuiltinHeads
compileExplicitEliminatorBuiltinsForMode doc tt mode = do
  builtins <- fmap M.fromList (mapM compileOne decls)
  pure (eliminatorBuiltins builtins)
  where
    decls =
      [ decl
      | decl <- explicitBuiltinDeclsForMode doc mode
      , case bdSpec decl of
          BDTransport -> False
          BDInductiveElim _ _ -> True
      ]

    compileOne decl =
      case bdSpec decl of
        BDTransport ->
          Left "validateDoctrine: internal error compiling explicit transport builtin as eliminator"
        BDInductiveElim scrutineeIx branches -> do
          builtin <- compileExplicitInductiveElimBuiltin (bdHead decl) scrutineeIx branches
          pure (bdHead decl, BuiltinInductiveElim builtin)

    compileExplicitInductiveElimBuiltin headName scrutineeIx branches = do
      sig <-
        case lookupTmHeadSig tt mode headName of
          Nothing ->
            Left
              ( "validateDoctrine: explicit builtin eliminator references unknown term head "
                  <> renderModeNameText mode
                  <> "."
                  <> renderGenNameText headName
              )
          Just sig -> Right sig
      (scrutineeRef, headParamByFamilyArg) <-
        case scrutineeFamilyShape sig scrutineeIx of
          Nothing ->
            Left
              ( "validateDoctrine: explicit builtin eliminator "
                  <> renderModeNameText mode
                  <> "."
                  <> renderGenNameText headName
                  <> " has an invalid scrutinee index"
              )
          Just shape ->
            Right shape
      if length branches == length (thsBinders sig)
        then Right ()
        else
          Left
            ( "validateDoctrine: explicit builtin eliminator "
                <> renderModeNameText mode
                <> "."
                <> renderGenNameText headName
                <> " has binder-branch arity mismatch"
            )
      let branchNames = map bbdCtor branches
      if length (S.fromList branchNames) == length branchNames
        then Right ()
        else
          Left
            ( "validateDoctrine: explicit builtin eliminator "
                <> renderModeNameText mode
                <> "."
                <> renderGenNameText headName
                <> " repeats a constructor branch"
            )
      compiledBranches <-
        mapM
          (uncurry (compileExplicitBranch sig scrutineeIx scrutineeRef headParamByFamilyArg))
          (zip branches (thsBinders sig))
      pure
        InductiveElimBuiltin
          { iebScrutineeIndex = scrutineeIx
          , iebScrutineeTyCon = scrutineeRef
          , iebBranches = compiledBranches
          }

    compileExplicitBranch sig scrutineeIx scrutineeRef headParamByFamilyArg branchDecl slot0 = do
      ctorSig <-
        case lookupTmHeadSig tt mode (bbdCtor branchDecl) of
          Nothing ->
            Left
              ( "validateDoctrine: explicit builtin eliminator branch references unknown constructor head "
                  <> renderModeNameText mode
                  <> "."
                  <> renderGenNameText (bbdCtor branchDecl)
              )
          Just ctorSig -> Right ctorSig
      if null (thsBinders ctorSig)
        then Right ()
        else
          Left
            ( "validateDoctrine: explicit builtin eliminator branch constructor "
                <> renderModeNameText mode
                <> "."
                <> renderGenNameText (bbdCtor branchDecl)
                <> " must not take binder arguments"
            )
      case objCode (thsRes ctorSig) of
        CTCon ref _ | ref == scrutineeRef ->
          Right ()
        _ ->
          Left
            ( "validateDoctrine: explicit builtin eliminator branch constructor "
                <> renderModeNameText mode
                <> "."
                <> renderGenNameText (bbdCtor branchDecl)
                <> " does not return the scrutinee family"
            )
      let recursiveCalls =
            M.fromList
              [ (i, sources)
              | (i, inputSort0) <- zip [0 :: Int ..] (thsInputs ctorSig)
              , Just sources <-
                  [ recursiveCallSourcesForInput
                      (thsParams sig)
                      scrutineeRef
                      headParamByFamilyArg
                      (thsParams ctorSig)
                      inputSort0
                  ]
              ]
      if length (bbdTmCtxInputs branchDecl) == length (bsTmCtx slot0)
        then Right ()
        else
          Left
            ( "validateDoctrine: explicit builtin eliminator branch "
                <> renderGenNameText (bbdCtor branchDecl)
                <> " has local tm-context arity mismatch"
            )
      if length (bbdInputs branchDecl) == length (bsDom slot0)
        then Right ()
        else
          Left
            ( "validateDoctrine: explicit builtin eliminator branch "
                <> renderGenNameText (bbdCtor branchDecl)
                <> " has input arity mismatch"
            )
      mapM_ (validateBranchSource ctorSig recursiveCalls) (bbdTmCtxInputs branchDecl)
      mapM_ (validateBranchSource ctorSig recursiveCalls) (bbdInputs branchDecl)
      validateExplicitBranchSelection tt sig scrutineeIx scrutineeRef headParamByFamilyArg ctorSig branchDecl slot0
      pure
        ElimBranchBuiltin
          { ebbCtorGen = bbdCtor branchDecl
          , ebbTmCtxInputs = bbdTmCtxInputs branchDecl
          , ebbInputs = bbdInputs branchDecl
          }
      where
        validateBranchSource ctorSig recursiveCalls source =
          case source of
            BISOuterHeadTmParam i ->
              case safeNth (thsParams sig) i of
                Just (GP_Tm _) -> Right ()
                Just (GP_Ty _) ->
                  Left "validateDoctrine: explicit builtin eliminator source outer_head_tm points at a type-valued head parameter"
                Nothing ->
                  Left "validateDoctrine: explicit builtin eliminator source outer_head_tm is out of bounds"
            BISCtorHeadTmParam i ->
              case safeNth (thsParams ctorSig) i of
                Just (GP_Tm _) -> Right ()
                Just (GP_Ty _) ->
                  Left "validateDoctrine: explicit builtin eliminator source ctor_head_tm points at a type-valued constructor parameter"
                Nothing ->
                  Left "validateDoctrine: explicit builtin eliminator source ctor_head_tm is out of bounds"
            BISOuterInput i ->
              case safeNth (thsInputs sig) i of
                Just _ -> Right ()
                Nothing -> Left "validateDoctrine: explicit builtin eliminator source outer_input is out of bounds"
            BISCtorField i ->
              case safeNth (thsInputs ctorSig) i of
                Just _ -> Right ()
                Nothing -> Left "validateDoctrine: explicit builtin eliminator source ctor_field is out of bounds"
            BISRecursiveResult i sources ->
              case M.lookup i recursiveCalls of
                Nothing ->
                  Left "validateDoctrine: explicit builtin eliminator source recursive_result points at a non-recursive constructor field"
                Just expected
                  | expected == sources ->
                      Right ()
                  | otherwise ->
                      Left
                        ( "validateDoctrine: explicit builtin eliminator source recursive_result has the wrong recursive head-argument mapping for constructor "
                            <> renderGenNameText (bbdCtor branchDecl)
                        )

    safeNth xs i
      | i < 0 =
          Nothing
      | otherwise =
          case drop i xs of
            (x:_) -> Just x
            [] -> Nothing

inferExtensionalBuiltinsForMode
  :: Doctrine
  -> TypeTheory
  -> ModeName
  -> S.Set GenName
  -> Either Text BuiltinHeads
inferExtensionalBuiltinsForMode _doc tt mode skipHeads = do
  builtins <- fmap (M.fromList . mapMaybe id) (mapM inferOne headsInMode)
  pure (extensionalBuiltins builtins)
  where
    headsInMode =
      [ (g, sig)
      | (g, sig) <- M.toList (termHeadsForMode tt mode)
      , S.notMember g skipHeads
      ]

    inferOne (g, sig) = do
      isTransport <- inferTransportBuiltinCandidate tt sig
      pure $
        if isTransport
          then Just (g, BuiltinTransport)
          else Nothing

inferEliminatorBuiltinsForMode
  :: Doctrine
  -> TypeTheory
  -> ModeName
  -> S.Set GenName
  -> Either Text BuiltinHeads
inferEliminatorBuiltinsForMode doc tt mode skipHeads = do
  ctorCasesByHead <- cellHeadConstructorCasesForMode doc tt mode
  builtins <- fmap (M.fromList . mapMaybe id) (mapM (inferOne ctorCasesByHead) headsInMode)
  pure (eliminatorBuiltins builtins)
  where
    headsInMode =
      [ (g, sig)
      | (g, sig) <- M.toList (termHeadsForMode tt mode)
      , S.notMember g skipHeads
      ]

    inferOne foldCasesByHead (g, sig) = do
      inductiveBuiltin <-
        case M.lookup g foldCasesByHead of
          Just ctorCases ->
            inferHeadCtorBuiltin g sig ctorCases
          _ ->
            Right Nothing
      pure (fmap (\builtin -> (g, BuiltinInductiveElim builtin)) inductiveBuiltin)

    inferHeadCtorBuiltin g sig ctorCases = do
      let ctorCasesByIndex =
            M.toList
              ( foldl
                  (\acc evidence -> M.insertWith (flip (<>)) (cceScrutineeIndex evidence) [evidence] acc)
                  M.empty
                  ctorCases
              )
      candidates <-
        fmap catMaybes $
          mapM
            (\(scrutineeIx, ctors) -> fmap (fmap (\builtin -> (scrutineeIx, builtin))) (inferInductiveElimBuiltinCandidate tt mode scrutineeIx sig ctors))
            ctorCasesByIndex
      case candidates of
        [] ->
          Right Nothing
        [(_, builtin)] ->
          Right (Just builtin)
        _ ->
          Left
            ( "validateDoctrine: ambiguous constructor-eliminator scrutinee for "
                <> renderModeNameText mode
                <> "."
                <> renderGenNameText g
                <> "."
                <> builtinElimExplicitDeclHint
            )

inferFunctionBuiltinsWithPolicy
  :: FragmentBuildPolicy
  -> Doctrine
  -> TypeTheory
  -> ModeName
  -> Either Text BuiltinHeads
inferFunctionBuiltinsWithPolicy policy doc tt mode =
  case fbpStrictBuiltinEvidence policy of
    True ->
      inferAndFinalizeFunctionBuiltins
        (fbpRequireBuiltinCtorEligibility policy)
        doc
        tt
        mode
    False ->
      case inferFunctionBuiltinForMode doc tt mode of
        Left _ -> Right emptyBuiltinHeads
        Right Nothing -> Right emptyBuiltinHeads
        Right (Just fb) ->
          case
            finalizeFunctionBuiltinForMode
              (fbpRequireBuiltinCtorEligibility policy)
              doc
              tt
              mode
              fb
          of
            Left _ -> Right emptyBuiltinHeads
            Right builtins -> Right builtins

inferExtensionalBuiltinsWithPolicy
  :: FragmentBuildPolicy
  -> Doctrine
  -> TypeTheory
  -> ModeName
  -> S.Set GenName
  -> Either Text BuiltinHeads
inferExtensionalBuiltinsWithPolicy policy doc tt mode skipHeads
  | not (fbpRequireBuiltinCtorEligibility policy) =
      Right emptyBuiltinHeads
  | fbpStrictBuiltinEvidence policy =
      inferExtensionalBuiltinsForMode doc tt mode skipHeads
  | otherwise =
      case inferExtensionalBuiltinsForMode doc tt mode skipHeads of
        Left _ -> Right emptyBuiltinHeads
        Right builtins -> Right builtins

inferEliminatorBuiltinsWithPolicy
  :: FragmentBuildPolicy
  -> Doctrine
  -> TypeTheory
  -> ModeName
  -> S.Set GenName
  -> Either Text BuiltinHeads
inferEliminatorBuiltinsWithPolicy policy doc tt mode skipHeads
  | not (fbpRequireBuiltinCtorEligibility policy) =
      Right emptyBuiltinHeads
  | fbpStrictBuiltinEvidence policy =
      inferEliminatorBuiltinsForMode doc tt mode skipHeads
  | otherwise =
      case inferEliminatorBuiltinsForMode doc tt mode skipHeads of
        Left _ -> Right emptyBuiltinHeads
        Right builtins -> Right builtins

compileExplicitExtensionalBuiltinsWithPolicy
  :: FragmentBuildPolicy
  -> Doctrine
  -> TypeTheory
  -> ModeName
  -> Either Text BuiltinHeads
compileExplicitExtensionalBuiltinsWithPolicy policy doc tt mode
  | fbpStrictBuiltinEvidence policy =
      compileExplicitTransportBuiltinsForMode doc tt mode
  | otherwise =
      case compileExplicitTransportBuiltinsForMode doc tt mode of
        Left _ -> Right emptyBuiltinHeads
        Right builtins -> Right builtins

compileExplicitEliminatorBuiltinsWithPolicy
  :: FragmentBuildPolicy
  -> Doctrine
  -> TypeTheory
  -> ModeName
  -> Either Text BuiltinHeads
compileExplicitEliminatorBuiltinsWithPolicy policy doc tt mode
  | fbpStrictBuiltinEvidence policy =
      compileExplicitEliminatorBuiltinsForMode doc tt mode
  | otherwise =
      case compileExplicitEliminatorBuiltinsForMode doc tt mode of
        Left _ -> Right emptyBuiltinHeads
        Right builtins -> Right builtins

data FragmentBuildPolicy = FragmentBuildPolicy
  { fbpStrictBuiltinEvidence :: Bool
  , fbpRequireBuiltinCtorEligibility :: Bool
  , fbpCheckTrustedRules :: Bool
  }

kernelFragmentPolicy :: FragmentBuildPolicy
kernelFragmentPolicy =
  FragmentBuildPolicy
    { fbpStrictBuiltinEvidence = True
    , fbpRequireBuiltinCtorEligibility = True
    , fbpCheckTrustedRules = True
    }

ctorEligibilityFragmentPolicy :: FragmentBuildPolicy
ctorEligibilityFragmentPolicy =
  FragmentBuildPolicy
    { fbpStrictBuiltinEvidence = True
    , fbpRequireBuiltinCtorEligibility = False
    , fbpCheckTrustedRules = False
    }

ctorEligibilityElabFragmentPolicy :: FragmentBuildPolicy
ctorEligibilityElabFragmentPolicy =
  FragmentBuildPolicy
    { fbpStrictBuiltinEvidence = False
    , fbpRequireBuiltinCtorEligibility = False
    , fbpCheckTrustedRules = False
    }

checkFragmentBuiltinRuleSeparation :: DefFragment -> Either Text ()
checkFragmentBuiltinRuleSeparation fragment =
  let builtinHeads = M.keysSet (bhHeadRoles (dfBuiltins fragment))
      overlapping =
        [ name
        | rule <- RS.trsRules (dfCompiledRules fragment)
        , Just name <- [RS.rootKey (RS.trLHS rule)]
        , S.member name builtinHeads
        ]
   in case S.toList (S.fromList overlapping) of
        [] -> Right ()
        bad ->
          Left
            ( "validateDoctrine: built-in computational heads may not also carry trusted user rewrite rules in the first unified slice (mode "
                <> renderModeNameText (dfMode fragment)
                <> ", overlapping heads = ["
                <> T.intercalate ", " (map renderGenNameText bad)
                <> "])"
            )

stripBuiltinEvidenceRules
  :: Doctrine
  -> TypeTheory
  -> ModeName
  -> BuiltinHeads
  -> TRS
  -> Either Text (S.Set GenName, TRS)
stripBuiltinEvidenceRules doc tt mode builtins trs = do
  ctorCasesByHead <- cellHeadConstructorCasesForMode doc tt mode
  let functionHeads =
        case bhFunctionSpace builtins of
          Just fb -> [fbAppGen fb]
          Nothing -> []
      extensionalHeads = M.keys (bhExtensionalHeads builtins)
      builtinElimHeads =
        [ g
        | (g, BuiltinInductiveElim _) <- M.toList (bhEliminators builtins)
        ]
      ruleCount g =
        length
          [ ()
          | rule <- RS.trsRules trs
          , RS.rootKey (RS.trLHS rule) == Just g
          ]
      evidenceCount g =
        functionEvidenceCount g + eliminatorEvidenceCount g
      functionEvidenceCount g =
        case bhFunctionSpace builtins of
          Just fb
            | g == fbAppGen fb ->
                length
                  [ ()
                  | rule <- RS.trsRules trs
                  , isFunctionBetaEvidenceRule fb rule
                  ]
          _ ->
              0
      eliminatorEvidenceCount g =
        length (M.findWithDefault [] g ctorCasesByHead)
      stripHeads =
        S.fromList
          [ g
          | g <- functionHeads <> extensionalHeads <> builtinElimHeads
          , ruleCount g > 0
          , ruleCount g == evidenceCount g
          ]
      bad =
        [ g
        | g <- functionHeads <> extensionalHeads <> builtinElimHeads
        , ruleCount g > 0
        , not (S.member g stripHeads)
        ]
  if null bad
    then
      Right
        ( stripHeads
        , mkTRS
            mode
            [ rule
            | rule <- RS.trsRules trs
            , maybe True (`S.notMember` stripHeads) (RS.rootKey (RS.trLHS rule))
            ]
        )
    else
      Left
        ( "validateDoctrine: inferred builtin heads still have non-evidence trusted rules in mode "
            <> renderModeNameText mode
            <> " (heads = ["
            <> T.intercalate ", " (map renderGenNameText bad)
            <> "])"
        )

isFunctionBetaEvidenceRule :: FunctionBuiltin -> RS.TRule -> Bool
isFunctionBetaEvidenceRule fb rule =
  case (RS.trLHS rule, RS.trRHS rule, RS.trRHSDiagram rule) of
    (TMHead g flatArgs [], rhs, _)
      | g == fbAppGen fb
      , length flatArgs >= 2 ->
          case splitAt (length flatArgs - 2) flatArgs of
            (headArgs, [THATm lamExpr, THATm (TMBound 0)]) ->
              case lamExpr of
                TMHead lamGen lamArgs [TBAHole hole]
                  | lamGen == fbLamGen fb
                  , lamArgs == headArgs ->
                      rhsMatches hole rhs
                _ ->
                  False
            _ ->
              False
    _ ->
      False
  where
    rhsMatches hole rhs =
      case rhs of
        Just (TMSplice hole' me [TMBound 0]) ->
          hole == hole' && null (mePath me) && meSrc me == meTgt me
        _ ->
          False

buildDefFragmentsWithPolicy
  :: FragmentBuildPolicy
  -> Doctrine
  -> TypeTheory
  -> M.Map ModeName TRS
  -> Either Text (M.Map ModeName DefFragment)
buildDefFragmentsWithPolicy policy doc tt0 trsByMode =
  do
    fragments <- finalizeFragments
    if fbpCheckTrustedRules policy
      then mapM_
        checkFragmentTermination
        (M.elems fragments)
      else Right ()
    pure fragments
  where
    modes = M.keys (mtModes (dModes doc))
    fragments0 = ttDefFragments tt0

    fragmentsWithTRS =
      M.fromList
        [ (mode, withTRS mode)
        | mode <- modes
        ]

    withTRS mode =
      let base = M.findWithDefault (emptyDefFragment mode) mode fragments0
          trs = M.findWithDefault (mkTRS mode []) mode trsByMode
       in base
            { dfCompiledRules = trs
            , dfBuiltins = emptyBuiltinHeads
            }

    ttWithTRS = tt0 { ttDefFragments = fragmentsWithTRS }

    functionBuiltinsByMode =
      M.fromList
        <$> mapM
          (\mode -> do
              builtins <- inferFunctionBuiltinsWithPolicy policy doc ttWithTRS mode
              pure (mode, builtins)
          )
          modes

    fragmentsWithFunctionBuiltins = do
      funBuiltins <- functionBuiltinsByMode
      pure
        ( M.fromList
            [ (mode, withModeBuiltins funBuiltins mode)
            | mode <- modes
            ]
        )
      where
        withModeBuiltins funBuiltins mode =
          let base = M.findWithDefault (withTRS mode) mode fragmentsWithTRS
              builtins = M.findWithDefault emptyBuiltinHeads mode funBuiltins
           in base { dfBuiltins = builtins }

    ttWithFunctionBuiltins = do
      fragments <- fragmentsWithFunctionBuiltins
      pure tt0 { ttDefFragments = fragments }

    explicitExtensionalBuiltinsByMode = do
      ttBuiltins <- ttWithFunctionBuiltins
      M.fromList
        <$> mapM
          (\mode -> do
              builtins <- compileExplicitExtensionalBuiltinsWithPolicy policy doc ttBuiltins mode
              pure (mode, builtins)
          )
          modes

    extensionalBuiltinsByMode = do
      ttBuiltins <- ttWithFunctionBuiltins
      M.fromList
        <$> mapM
          (\mode -> do
              builtins <-
                inferExtensionalBuiltinsWithPolicy
                  policy
                  doc
                  ttBuiltins
                  mode
                  (explicitExtensionalHeadSetForMode doc mode)
              pure (mode, builtins)
          )
          modes

    explicitEliminatorBuiltinsByMode = do
      ttBuiltins <- ttWithFunctionBuiltins
      M.fromList
        <$> mapM
          (\mode -> do
              builtins <- compileExplicitEliminatorBuiltinsWithPolicy policy doc ttBuiltins mode
              pure (mode, builtins)
          )
          modes

    eliminatorBuiltinsByMode = do
      ttBuiltins <- ttWithFunctionBuiltins
      M.fromList
        <$> mapM
          (\mode -> do
              builtins <-
                inferEliminatorBuiltinsWithPolicy
                  policy
                  doc
                  ttBuiltins
                  mode
                  (explicitEliminatorHeadSetForMode doc mode)
              pure (mode, builtins)
          )
          modes

    finalizeMode mode = do
      funBuiltins <- M.findWithDefault emptyBuiltinHeads mode <$> functionBuiltinsByMode
      explicitExtBuiltins <- M.findWithDefault emptyBuiltinHeads mode <$> explicitExtensionalBuiltinsByMode
      extBuiltins <- M.findWithDefault emptyBuiltinHeads mode <$> extensionalBuiltinsByMode
      explicitElimBuiltins <- M.findWithDefault emptyBuiltinHeads mode <$> explicitEliminatorBuiltinsByMode
      elimBuiltins <- M.findWithDefault emptyBuiltinHeads mode <$> eliminatorBuiltinsByMode
      builtins <-
        mergeBuiltinHeads funBuiltins explicitExtBuiltins
          >>= (`mergeBuiltinHeads` extBuiltins)
          >>= (`mergeBuiltinHeads` explicitElimBuiltins)
          >>= (`mergeBuiltinHeads` elimBuiltins)
      let base = M.findWithDefault (withTRS mode) mode fragmentsWithTRS
      (stripHeads, trs') <- stripBuiltinEvidenceRules doc tt0 mode builtins (dfCompiledRules base)
      let fragment =
            base
              { dfRules =
                  [ rule
                  | rule <- dfRules base
                  , maybe True (`S.notMember` stripHeads) (rawRuleRootHead rule)
                  ]
              , dfCompiledRules = trs'
              , dfBuiltins = builtins
              }
      checkFragmentBuiltinRuleSeparation fragment
      pure (mode, fragment)
    finalizeFragments = M.fromList <$> mapM finalizeMode modes

    rawRuleRootHead rule =
      case dOut lhsDiag of
        [outPid] ->
          case producerEdge lhsDiag outPid of
            Just edge ->
              case ePayload edge of
                PGen g _ _ -> Just g
                _ -> Nothing
            Nothing -> Nothing
        _ -> Nothing
      where
        lhsDiag = unTerm (trLHS rule)

    producerEdge diag pid = do
      eid <- IM.lookup (unPortId pid) (dProd diag)
      edgeId <- eid
      IM.lookup (unEdgeId edgeId) (dEdges diag)

buildCompiledFragments
  :: Doctrine
  -> TypeTheory
  -> M.Map ModeName TRS
  -> Either Text (M.Map ModeName DefFragment)
buildCompiledFragments =
  buildDefFragmentsWithPolicy kernelFragmentPolicy

buildCtorEligibilityElabFragments
  :: Doctrine
  -> TypeTheory
  -> M.Map ModeName TRS
  -> Either Text (M.Map ModeName DefFragment)
buildCtorEligibilityElabFragments =
  buildDefFragmentsWithPolicy ctorEligibilityElabFragmentPolicy

renderRootSymbols :: TRS -> Text
renderRootSymbols trs =
  if null names
    then "(none)"
    else T.intercalate ", " names
  where
    names = S.toList (S.fromList (mapMaybe rootName (RS.trsRules trs)))
    rootName rule =
      case RS.trLHS rule of
        TMGen (GenName name) _ -> Just name
        _ -> Nothing

renderFragmentRules :: TRS -> Text
renderFragmentRules trs =
  if null linesOut
    then "    (none)"
    else T.unlines [ "    " <> line | line <- linesOut ]
  where
    linesOut =
      [ RS.trName rule <> ": " <> T.pack (show (RS.trLHS rule)) <> " -> " <> renderRuleRHS rule
      | rule <- RS.trsRules trs
      ]
    renderRuleRHS rule =
      case RS.trRHS rule of
        Just rhs -> T.pack (show rhs)
        Nothing ->
          case RS.trRHSDiagram rule of
            Just rhsDiag -> "<diagram-backed rhs " <> T.pack (show rhsDiag) <> ">"
            Nothing -> "<missing rhs>"

derivedTmHeads :: Doctrine -> CtorTables -> M.Map ModeName (M.Map GenName TmHeadSig)
derivedTmHeads doc ctorTables =
  M.fromList
    [ (mode, heads)
    | (mode, table) <- M.toList (dGens doc)
    , let heads =
            M.fromList
              [ (gdName gd, sig)
              | gd <- M.elems table
              , let GenName gName = gdName gd
              , not (isTypeDeclGenNameInTables doc ctorTables mode (ObjName gName))
              , Just sig <- [tmHeadSigForGenDecl gd]
              ]
    , not (M.null heads)
    ]

derivedGenArgSigs :: Doctrine -> M.Map ModeName (M.Map GenName GenArgSig)
derivedGenArgSigs doc =
  M.map
    ( M.map
        (\gd -> GenArgSig { gasParams = gdParams gd })
    )
    (dGens doc)

derivedDiagramRules :: Doctrine -> M.Map ModeName [Cell2]
derivedDiagramRules doc =
  M.fromListWith (<>)
    [ (dMode (c2LHS cell), [cell])
    | cell <- dCells2 doc
    ]

derivedTmRules :: Doctrine -> M.Map ModeName (M.Map GenName TmHeadSig) -> Either Text (M.Map ModeName [TmRule])
derivedTmRules doc tmFuns =
  fmap (M.fromListWith (<>)) $
    foldM collect [] (dCells2 doc)
  where
    collect acc cell
      | c2Class cell /= Computational =
          Right acc
      | otherwise =
          foldM (collectOne cell) acc (oriented cell)

    collectOne cell acc (lhs, rhs) =
      let mode = dMode lhs
       in case M.lookup mode tmFuns of
            Nothing -> Right acc
            Just funs -> do
              rule <- cellPairToTmRule funs (c2TyVars cell) (c2TmVars cell) lhs rhs
              Right ((mode, [rule]) : acc)

    oriented cell =
      case c2Orient cell of
        LR -> [(c2LHS cell, c2RHS cell)]
        RL -> [(c2RHS cell, c2LHS cell)]
        Bidirectional -> [(c2LHS cell, c2RHS cell), (c2RHS cell, c2LHS cell)]
        Unoriented -> []

cellPairToTmRule :: M.Map GenName TmHeadSig -> [TmVar] -> [TmVar] -> Diagram -> Diagram -> Either Text TmRule
cellPairToTmRule heads tyVars tmVars lhs0 rhs0 = do
  boundaryVars <- mkInputVars lhs0
  let vars = boundaryVars <> tmVars
  let varCtx = map tmvSort vars
  lhs <- mapLeft "lhs" (weakenDiagramTmCtxTo varCtx lhs0)
  rhs <- mapLeft "rhs" (weakenDiagramTmCtxTo varCtx rhs0)
  mapLeft "lhs" (validateDiagram lhs)
  mapLeft "rhs" (validateDiagram rhs)
  mapLeft "lhs" (ensureRuleSurface False lhs)
  mapLeft "rhs" (ensureRuleSurface True rhs)
  pure TmRule { trTyVars = tyVars, trVars = vars, trLHS = TermDiagram lhs, trRHS = TermDiagram rhs }
  where
    mapLeft side =
      first
        ( \err ->
            "cellPairToTmRule: "
              <> side
              <> " of computational rule failed: "
              <> err
        )

    ensureRuleSurface allowSplice d = mapM_ (checkEdge allowSplice) (IM.elems (dEdges d))
    checkEdge allowSplice edge =
      case ePayload edge of
        PGen _ _ _ -> Right ()
        PTmMeta _ -> Right ()
        PTmLit _ -> Right ()
        PInternalDrop -> Right ()
        PSplice _ _
          | allowSplice ->
              Right ()
          | otherwise ->
              Left "splice nodes are only allowed on trusted rule right-hand sides"
        _ -> Left "non-term payload in trusted rewrite rule"

mkInputVars :: Diagram -> Either Text [TmVar]
mkInputVars diag =
  mapM mkOne (zip [0 :: Int ..] (dIn diag))
  where
    mkOne (i, pid) = do
      sortTy <-
        case IM.lookup (unPortId pid) (dPortObj diag) of
          Nothing -> Left "trusted rule boundary input is missing a sort"
          Just ty -> Right ty
      pure TmVar { tmvName = "_x" <> T.pack (show i), tmvSort = sortTy, tmvScope = 0, tmvOwnerMode = Nothing }

validateDoctrine :: Doctrine -> Either Text ()
validateDoctrine doc = do
  checkModeTheory (dModes doc)
  if all (`M.member` mtModes (dModes doc)) (S.toList (dAcyclicModes doc))
    then Right ()
    else Left "validateDoctrine: acyclic mode references unknown mode"
  ctorTables <- deriveCtorTables doc
  tt <- mkTypeTheoryFromTables doc ctorTables
  checkComprehensionDecls doc ctorTables
  checkClassifierLiftUniverseCompatibility doc tt
  mapM_ (checkGenTable doc tt ctorTables) (M.toList (dGens doc))
  mapM_ (checkCell doc tt) (dCells2 doc)
  mapM_ (checkAction doc tt ctorTables) (M.toList (dActions doc))
  mapM_ (checkModeTransform doc) (M.elems (mtTransforms (dModes doc)))
  mapM_ (checkObligation doc tt) (dObligations doc)
  pure ()

doctrineCheck :: Doctrine -> Either Text ()
doctrineCheck = validateDoctrine

checkClassifierLiftUniverseCompatibility :: Doctrine -> TypeTheory -> Either Text ()
checkClassifierLiftUniverseCompatibility doc tt =
  mapM_ checkOne classifiedModalities
  where
    classDecl mode = M.lookup mode (mtClassifiedBy (dModes doc))

    classifiedModalities =
      [ (modName, srcClass, tgtClass)
      | (modName, decl) <- M.toList (mtDecls (dModes doc))
      , Just srcClass <- [classDecl (mdSrc decl)]
      , Just tgtClass <- [classDecl (mdTgt decl)]
      ]

    checkOne (modName, srcClass, tgtClass) = do
      liftExpr <-
        case classifierLiftForModality (dModes doc) modName of
          Left err -> Left ("validateDoctrine: " <> err)
          Right me -> Right me
      transportedNorm <- normalizeObjDeep tt (liftUniverse liftExpr (cdUniverse srcClass))
      targetNorm <- normalizeObjDeep tt (cdUniverse tgtClass)
      ok <- defEqObj tt [] transportedNorm targetNorm
      if ok
        then Right ()
        else
          Left
            ( "validateDoctrine: classifier lift universe mismatch for modality "
                <> renderMod modName
                <> " (expected "
                <> T.pack (show targetNorm)
                <> ", got "
                <> T.pack (show transportedNorm)
                <> ")"
            )

    liftUniverse liftExpr universe =
      Obj
        { objOwnerMode = meTgt liftExpr
        , objCode = CTLift liftExpr (objCode universe)
        }

    renderMod (ModName n) = n

checkComprehensionDecls :: Doctrine -> CtorTables -> Either Text ()
checkComprehensionDecls doc ctorTables =
  mapM_ checkOne (M.toList (mtClassifiedBy (dModes doc)))
  where
    checkOne (ownerMode, decl) =
      case cdComp decl of
        Nothing ->
          Left
            ( "validateDoctrine: mode "
                <> renderMode ownerMode
                <> " is classified and requires a comprehension declaration"
            )
        Just comp -> do
          checkField ownerMode "ctx_ext" (compCtxExt comp)
          checkField ownerMode "var" (compVar comp)
          checkField ownerMode "reindex" (compReindex comp)

    checkField ownerMode fieldName genName = do
      maybeGen <- lookupCompGen ownerMode fieldName genName
      case maybeGen of
        Nothing -> Right ()
        Just gen -> do
          checkNotCtor ownerMode fieldName genName
          checkShape ownerMode fieldName genName gen

    lookupCompGen ownerMode fieldName genName =
      case M.lookup ownerMode (dGens doc) >>= M.lookup genName of
        Just gd -> Right (Just gd)
        Nothing ->
          Left
            ( "validateDoctrine: comprehension "
                <> fieldName
                <> " generator "
                <> renderMode ownerMode
                <> "."
                <> renderGen genName
                <> " is not declared"
            )

    checkShape ownerMode fieldName genName gd = do
      case gdDom gd of
        [InPort _] -> Right ()
        _ ->
          Left
            ( "validateDoctrine: comprehension "
                <> fieldName
                <> " generator "
                <> renderMode ownerMode
                <> "."
                <> renderGen genName
                <> " must have exactly one input port and no binder inputs"
            )
      case gdCod gd of
        [_] -> Right ()
        _ ->
          Left
            ( "validateDoctrine: comprehension "
                <> fieldName
                <> " generator "
                <> renderMode ownerMode
                <> "."
                <> renderGen genName
                <> " must have exactly one output"
            )

    checkNotCtor ownerMode fieldName genName =
      if isTypeDeclGenNameInTables doc ctorTables ownerMode (ObjName (renderGen genName))
        then
          Left
            ( "validateDoctrine: comprehension "
                <> fieldName
                <> " generator "
                <> renderMode ownerMode
                <> "."
                <> renderGen genName
                <> " resolves as a constructor-like declaration"
            )
        else Right ()

    renderMode (ModeName n) = n
    renderGen (GenName n) = n

modeIsAcyclic :: Doctrine -> ModeName -> Bool
modeIsAcyclic doc mode = mode `S.member` dAcyclicModes doc

deriveCtorTables :: Doctrine -> Either Text (M.Map ModeName (M.Map ObjName CtorSig))
deriveCtorTables =
  deriveCtorTablesWithPolicy ctorEligibilityFragmentPolicy

deriveCtorTablesForElab :: Doctrine -> Either Text (M.Map ModeName (M.Map ObjName CtorSig))
deriveCtorTablesForElab =
  deriveCtorTablesWithPolicy ctorEligibilityElabFragmentPolicy

deriveCtorTablesWithPolicy
  :: FragmentBuildPolicy
  -> Doctrine
  -> Either Text (M.Map ModeName (M.Map ObjName CtorSig))
deriveCtorTablesWithPolicy fragmentPolicy doc = do
  ownerModes <- classificationOrder (dModes doc)
  seedPairs <- mapM seedForOwner ownerModes
  let seed = M.fromList seedPairs
  foldM growOwnerOrdered seed ownerModes
  where
    buildTypeTheory tables = do
      tt0 <- doctrineTypeTheoryBaseFromTables doc tables
      trs <- compileAllTermRules tt0
      fragments <- buildDefFragmentsWithPolicy fragmentPolicy doc tt0 trs
      pure tt0 { ttDefFragments = fragments }

    seedForOwner ownerMode = do
      case ownerClassifier ownerMode of
        -- Policy: unclassified modes are allowed, but they never get constructor tables.
        Nothing -> pure (ownerMode, M.empty)
        Just classifierMode -> do
          implicit <- implicitForOwner classifierMode ownerMode
          pure (ownerMode, implicit)

    growOwnerOrdered acc ownerMode =
      case ownerClassifier ownerMode of
        Nothing -> Right acc
        Just classifierMode ->
          if classifierMode == ownerMode
            then growOwnerSelfFixedPoint acc ownerMode
            else growOwnerOnce acc ownerMode

    growOwnerOnce acc ownerMode = do
      tt <- buildTypeTheory acc
      let existing = M.findWithDefault M.empty ownerMode acc
      discovered <- eligibleForOwner tt ownerMode
      merged <- mergeCtorTables existing discovered
      pure (M.insert ownerMode merged acc)

    growOwnerSelfFixedPoint acc0 ownerMode =
      iterateSelf (maxIterations ownerMode) acc0
      where
        iterateSelf remaining acc
          | remaining <= (0 :: Int) =
              Left "deriveCtorTables: self-classified constructor table did not converge"
          | otherwise = do
              acc' <- growOwnerOnce acc ownerMode
              let oldTable = M.findWithDefault M.empty ownerMode acc
              let newTable = M.findWithDefault M.empty ownerMode acc'
              if newTable == oldTable
                then Right acc'
                else iterateSelf (remaining - 1) acc'

    maxIterations ownerMode =
      1 + length (candidateCtors ownerMode)

    implicitForOwner classifierMode ownerMode =
      case modeUniverseObj (dModes doc) ownerMode of
        Just universe -> do
          universeNorm <- normalizeObjExpr (dModes doc) universe
          implicitUniverseCtor classifierMode universeNorm
        _ -> provisionalCtorsForOwner ownerMode

    eligibleForOwner tt ownerMode = do
      case ownerClassifier ownerMode of
        Nothing -> Right M.empty
        Just classifierMode ->
          case modeUniverseObj (dModes doc) ownerMode of
            Just universe -> do
              mUniverseNorm <- normalizeUniverseIfReady tt ownerMode universe
              case mUniverseNorm of
                Just universeNorm -> do
                  fromGens <- foldM (addCtor tt ownerMode universeNorm) M.empty (candidateCtors ownerMode)
                  implicit <- implicitUniverseCtor classifierMode universeNorm
                  mergeCtorTables fromGens implicit
                Nothing ->
                  provisionalCtorsForOwner ownerMode
            _ -> provisionalCtorsForOwner ownerMode

    candidateCtors ownerMode =
      case ownerClassifier ownerMode of
        Nothing -> []
        Just classifierMode ->
          [ gd
          | gd <- M.elems (M.findWithDefault M.empty classifierMode (dGens doc))
          , isCtorLikeGen gd
          ]

    implicitUniverseCtor classifierMode universeNorm =
      case implicitUniverseCtorRef classifierMode (objCode universeNorm) of
        Just ref -> Right (M.singleton (orName ref) (CtorSig []))
        Nothing -> Right M.empty

    implicitUniverseCtorRef classifierMode code =
      case code of
        CTCon ref []
          | orMode ref == classifierMode ->
              Just ref
        _ | Just ref <- pendingUniverseSeedInnerRef code
            , orMode ref == classifierMode ->
              Just ref
        CTLift _ inner ->
          implicitUniverseCtorRef classifierMode inner
        _ ->
          Nothing

    normalizeUniverseIfReady tt ownerMode universe = do
      universeNorm <- normalizeObjExpr (dModes doc) universe
      case universeNorm of
        Obj _ (CTCon _ []) ->
          -- Bare universe names are allowed as implicit classifier vocabulary.
          Right (Just universeNorm)
        _ -> do
          let classifierMode = modeClassifierMode (dModes doc) ownerMode
          case checkCodeWellFormed tt classifierMode (objCode universeNorm) of
            Right () -> Right (Just universeNorm)
            Left _ -> Right Nothing

    provisionalCtorsForOwner ownerMode =
      foldM
        (\acc gd -> do
          sig <- ctorSigFromGen gd
          insertCtorSig (genToObjName (gdName gd)) sig acc)
        M.empty
        (candidateCtors ownerMode)

    addCtor tt ownerMode universeNorm acc gd =
      case gdCod gd of
        [codTy] -> do
          include <- eligibilityDefEq tt ownerMode gd (map tmvSort (gdTmVars gd)) codTy universeNorm
          if include
            then do
              sig <- ctorSigFromGen gd
              insertCtorSig (genToObjName (gdName gd)) sig acc
            else Right acc
        _ -> Right acc

    eligibilityDefEq tt ownerMode gd tmCtx codTy universeNorm =
      case shallowCtorEligibilityMismatch codTy universeNorm of
        Right True -> Right False
        Right False ->
          case defEqObj tt tmCtx codTy universeNorm of
            Right ok -> Right ok
            Left err
              | shouldDeferEligibilityError err ->
                  Right False
            Left err ->
              Left
                ( "deriveCtorTables: constructor eligibility defeq failed for "
                    <> renderMode (gdMode gd)
                    <> "."
                    <> renderGen (gdName gd)
                    <> " while checking owner mode "
                    <> renderMode ownerMode
                    <> ": "
                    <> err
                )
        Left err ->
          Left
            ( "deriveCtorTables: constructor eligibility head normalization failed for "
                <> renderMode (gdMode gd)
                <> "."
                <> renderGen (gdName gd)
                <> " while checking owner mode "
                <> renderMode ownerMode
                <> ": "
                <> err
            )

    shouldDeferEligibilityError err =
      "unknown type constructor" `T.isInfixOf` err

    shallowCtorEligibilityMismatch codTy universeNorm = do
      codTy' <- normalizeObjExpr (dModes doc) codTy
      universeNorm' <- normalizeObjExpr (dModes doc) universeNorm
      pure (headMismatch codTy' universeNorm')

    headMismatch lhs rhs =
      case (objCode lhs, objCode rhs) of
        (CTCon refL _, CTCon refR _) -> refL /= refR
        _ -> False

    mergeCtorTables a b =
      foldM
        (\acc (name, sig) -> insertCtorSig name sig acc)
        a
        (M.toList b)

    genToObjName (GenName name) = ObjName name
    ownerClassifier mode = cdClassifier <$> classifierOfMode (dModes doc) mode

isCtorLikeGen :: GenDecl -> Bool
isCtorLikeGen gd =
  null (gdDom gd)

ctorSigFromGen :: GenDecl -> Either Text CtorSig
ctorSigFromGen gd = do
  validateParamTeleScope (gdParams gd)
  canonicalizeCtorSig (gdParams gd)
  where
    renderGen (GenName name) = name

    validateParamTeleScope params = do
      teleDistinctNames params
      go [] params

    go _ [] = Right ()
    go earlier (param:rest) =
      case param of
        GP_Ty v -> do
          if S.null (boundTmIndicesObj (tmvSort v))
            then go (earlier <> [v]) rest
            else
              Left
                ( "constructor generator `"
                    <> renderGen (gdName gd)
                    <> "` has type parameter `"
                    <> tmvName v
                    <> "` whose sort contains bound term indices"
                )
        GP_Tm v -> do
          let allowed = S.fromList earlier
          let free = freeVarsObj (tmvSort v)
          let bad = S.difference free allowed
          if not (S.null bad)
            then
              Left
                ( "constructor generator `"
                    <> renderGen (gdName gd)
                    <> "` has term parameter `"
                    <> tmvName v
                    <> "` whose sort refers to out-of-scope parameters"
                )
            else
              if not (S.null (boundTmIndicesObj (tmvSort v)))
                then
                  Left
                    ( "constructor generator `"
                        <> renderGen (gdName gd)
                        <> "` has term parameter `"
                        <> tmvName v
                        <> "` whose sort contains bound term indices"
                    )
                else go (earlier <> [v]) rest

insertCtorSig
  :: ObjName
  -> CtorSig
  -> M.Map ObjName CtorSig
  -> Either Text (M.Map ObjName CtorSig)
insertCtorSig name sig acc =
  case M.lookup name acc of
    Nothing -> Right (M.insert name sig acc)
    Just sig0
      | sig0 == sig -> Right acc
      | otherwise ->
          Left
            ( "duplicate constructor `"
                <> unObjName name
                <> "` with incompatible signatures in classifier vocabulary"
            )

lookupCtorRefForOwnerInTables :: Doctrine -> CtorTables -> ModeName -> ObjName -> Maybe ObjRef
lookupCtorRefForOwnerInTables doc tables ownerMode ctorName =
  case classifierOfMode (dModes doc) ownerMode of
    Nothing -> Nothing
    Just decl ->
      case M.lookup ctorName ownerTable of
        Nothing -> Nothing
        Just _ -> Just (ObjRef (cdClassifier decl) ctorName)
      where
        ownerTable = M.findWithDefault M.empty ownerMode tables

lookupCtorSigForOwnerInTables :: Doctrine -> CtorTables -> ModeName -> ObjRef -> Either Text CtorSig
lookupCtorSigForOwnerInTables doc tables ownerMode ref = do
  classifierMode <-
    case classifierModeForCtorUse (dModes doc) ownerMode of
      Right mode -> Right mode
      Left err ->
        Left
          ( err
              <> " (while checking constructor "
              <> renderCtorRef ref
              <> ")"
          )
  if orMode ref == classifierMode
    then Right ()
    else
      Left
        ( "constructor qualifier mode mismatch: owner mode "
            <> renderMode ownerMode
            <> " is classified by "
            <> renderMode classifierMode
        )
  let table = M.findWithDefault M.empty ownerMode tables
  case M.lookup (orName ref) table of
    Nothing ->
      Left
        ( "unknown constructor `"
            <> unObjName (orName ref)
            <> "` for owner mode "
            <> renderMode ownerMode
            <> " (classifier "
            <> renderMode classifierMode
            <> "); available: "
            <> renderCtorNames (M.keys table)
        )
    Just sig -> Right sig
  where
    renderCtorRef ref' = renderMode (orMode ref') <> "." <> unObjName (orName ref')
    renderCtorNames [] = "(none)"
    renderCtorNames names = T.intercalate ", " (map unObjName names)

allCtorSigsInTables :: Doctrine -> CtorTables -> Either Text [(ObjRef, CtorSig)]
allCtorSigsInTables doc tables = do
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
              | otherwise -> Left "ambiguous constructor signature across owner modes"

lookupCtorSigByRefInTables :: Doctrine -> CtorTables -> ObjRef -> Either Text CtorSig
lookupCtorSigByRefInTables doc tables ref = do
  let sigs =
        [ sig
        | (ownerMode, table) <- M.toList tables
        , modeClassifierMode (dModes doc) ownerMode == orMode ref
        , Just sig <- [M.lookup (orName ref) table]
        ]
  case L.nub sigs of
    [] -> Left "unknown constructor"
    [sig] -> Right sig
    _ -> Left "ambiguous constructor signature across owner modes"

checkModeTheory :: ModeTheory -> Either Text ()
checkModeTheory = checkWellFormed

checkGenTable :: Doctrine -> TypeTheory -> CtorTables -> (ModeName, M.Map GenName GenDecl) -> Either Text ()
checkGenTable doc tt ctorTables (mode, gens)
  | M.member mode (mtModes (dModes doc)) = mapM_ (checkGen doc tt ctorTables mode) (M.elems gens)
  | otherwise = Left "validateDoctrine: generators for unknown mode"

checkGen :: Doctrine -> TypeTheory -> CtorTables -> ModeName -> GenDecl -> Either Text ()
checkGen doc tt ctorTables mode gd
  | gdMode gd /= mode = Left "validateDoctrine: generator stored under wrong mode"
  | otherwise = do
      checkParamTele doc tt ("validateDoctrine: generator " <> renderGen (gdName gd)) (gdParams gd)
      mapM_ (checkInputShape doc tt mode (gdTyVars gd) (gdTmVars gd)) (gdDom gd)
      checkContext doc tt mode (gdTyVars gd) (gdTmVars gd) [] (gdCod gd)
      checkGenLiteralKind doc ctorTables gd

checkInputShape :: Doctrine -> TypeTheory -> ModeName -> [TmVar] -> [TmVar] -> InputShape -> Either Text ()
checkInputShape doc tt expectedMode tyvars tmvars shape =
  case shape of
    InPort ty -> checkBoundaryType doc tt expectedMode tyvars tmvars [] ty
    InBinder bs -> checkBinderSig doc tt expectedMode tyvars tmvars bs

checkBinderSig :: Doctrine -> TypeTheory -> ModeName -> [TmVar] -> [TmVar] -> BinderSig -> Either Text ()
checkBinderSig doc tt expectedMode tyvars tmvars bs = do
  checkTmCtxTele (bsTmCtx bs)
  checkContext doc tt expectedMode tyvars tmvars (bsTmCtx bs) (bsDom bs)
  checkContext doc tt expectedMode tyvars tmvars (bsTmCtx bs) (bsCod bs)
  where
    checkTmCtxTele ctx =
      mapM_ checkAt (zip [0 :: Int ..] ctx)

    checkAt (i, ty) = do
      checkType doc tt tyvars tmvars (take i (bsTmCtx bs)) ty
      Right ()

checkCell :: Doctrine -> TypeTheory -> Cell2 -> Either Text ()
checkCell doc tt cell = do
  validateDiagram (c2LHS cell)
  validateDiagram (c2RHS cell)
  if S.null (spliceMetaVarsDiagram (c2LHS cell))
    then Right ()
    else Left "validateDoctrine: splice nodes are not allowed in rule LHS"
  if IM.size (dEdges (c2LHS cell)) <= 0
    then Left "validateDoctrine: empty LHS rules are disallowed (use an explicit marker generator if you need insertion)"
    else Right ()
  checkParamTele doc tt ("validateDoctrine: cell " <> c2Name cell) (c2Params cell)
  if dMode (c2LHS cell) /= dMode (c2RHS cell)
    then Left "validateDoctrine: cell has mode mismatch"
    else if dTmCtx (c2LHS cell) /= dTmCtx (c2RHS cell)
      then Left "validateDoctrine: cell has term-context mismatch"
    else do
      let tmCtx = dTmCtx (c2LHS cell)
      ctxL <- diagramDom (c2LHS cell)
      ctxR <- diagramDom (c2RHS cell)
      _ <-
        case unifyCtxCompat tt tmCtx ctxL ctxR of
          Left err -> Left ("validateDoctrine: cell " <> c2Name cell <> " domain mismatch: " <> err)
          Right subst -> Right subst
      codL <- diagramCod (c2LHS cell)
      codR <- diagramCod (c2RHS cell)
      _ <-
        case unifyCtxCompat tt tmCtx codL codR of
          Left err -> Left ("validateDoctrine: cell " <> c2Name cell <> " codomain mismatch: " <> err)
          Right subst -> Right subst
      let lhsVars = freeVarsDiagram (c2LHS cell)
      let rhsVars = freeVarsDiagram (c2RHS cell)
      let declaredVars = S.fromList (c2TyVars cell <> c2TmVars cell)
      if S.isSubsetOf rhsVars (S.union lhsVars declaredVars)
        then Right ()
        else Left "validateDoctrine: RHS introduces fresh type variables"
      if S.isSubsetOf rhsVars (S.union lhsVars declaredVars)
        then Right ()
        else Left "validateDoctrine: RHS introduces fresh term variables"
      let vars = S.union lhsVars rhsVars
      if S.isSubsetOf vars declaredVars
        then Right ()
        else Left "validateDoctrine: cell uses undeclared type variables"
      if S.isSubsetOf vars declaredVars
        then Right ()
        else Left "validateDoctrine: cell uses undeclared term variables"
      let lhsCapturedMetas = binderArgMetaVarsDiagram (c2LHS cell)
      let rhsReferencedMetas = S.union (binderArgMetaVarsDiagram (c2RHS cell)) (spliceMetaVarsDiagram (c2RHS cell))
      if S.isSubsetOf rhsReferencedMetas lhsCapturedMetas
        then Right ()
        else Left "validateDoctrine: RHS references binder metas not captured by LHS binder arguments"

checkContext :: Doctrine -> TypeTheory -> ModeName -> [TmVar] -> [TmVar] -> [Obj] -> Context -> Either Text ()
checkContext doc tt expectedMode tyvars tmvars tmCtx ctx = mapM_ (checkBoundaryType doc tt expectedMode tyvars tmvars tmCtx) ctx

checkBoundaryType :: Doctrine -> TypeTheory -> ModeName -> [TmVar] -> [TmVar] -> [Obj] -> Obj -> Either Text ()
checkBoundaryType doc tt expectedMode tyvars tmvars tmCtx ty = do
  checkType doc tt tyvars tmvars tmCtx ty
  if objOwnerMode ty == expectedMode
    then Right ()
    else Left "validateDoctrine: generator boundary mode mismatch"

checkType :: Doctrine -> TypeTheory -> [TmVar] -> [TmVar] -> [Obj] -> Obj -> Either Text ()
checkType doc tt tyvars tmvars tmCtx ty =
  case ty of
    OVar v ->
      if v `elem` tyvars
        then
          if M.member (tyVarOwnerMode v) (mtModes (dModes doc))
            then Right ()
            else Left "validateDoctrine: type variable has unknown mode"
        else Left "validateDoctrine: unknown type variable"
    OCon ref args -> do
      sig <- lookupCtorSigForOwnerInTables doc (ttCtorTablesByOwner tt) (objOwnerMode ty) ref
      if length (csParams sig) /= length args
        then Left "validateDoctrine: type constructor arity mismatch"
        else do
          _ <- foldM checkArg emptySubst (zip (csParams sig) args)
          Right ()
    OLift me inner -> do
      let owner = objOwnerMode ty
      let expectedClassifier = modeClassifierMode (dModes doc) owner
      if meTgt me == expectedClassifier
        then Right ()
        else Left "validateDoctrine: lift target does not match owner classifier mode"
      checkType doc tt tyvars tmvars tmCtx inner
      _ <- normalizeObjExpr (dModes doc) ty
      Right ()
  where
    bindArg v arg subst = do
      singleton <- mkSubst [(v, arg)]
      composeSubst tt singleton subst

    checkArg subst (GP_Ty v, OAObj argTy) = do
      let expectedOwner = tmVarOwner v
      checkType doc tt tyvars tmvars tmCtx argTy
      if objOwnerMode argTy == expectedOwner
        then bindArg v (CAObj argTy) subst
        else Left "validateDoctrine: type constructor argument mode mismatch"
    checkArg subst (GP_Tm v, OATm tmTerm) = do
      expectedSort <- applySubstObj tt subst (tmvSort v)
      checkType doc tt tyvars tmvars tmCtx expectedSort
      checkTmTerm doc tt tyvars tmvars tmCtx expectedSort tmTerm
      bindArg v (CATm tmTerm) subst
    checkArg _ _ = Left "validateDoctrine: type argument kind mismatch"

checkTmTerm :: Doctrine -> TypeTheory -> [TmVar] -> [TmVar] -> [Obj] -> Obj -> TermDiagram -> Either Text ()
checkTmTerm doc tt tyvars tmvars tmCtx expectedSort tm =
  do
    mapM_ checkMetaVar (S.toList (freeTermMetas tm))
    _ <- termToDiagram tt tmCtx expectedSort tm
    pure ()
  where
    freeTermMetas (TermDiagram diag) =
      S.fromList
        [ v
        | edge <- IM.elems (dEdges diag)
        , PTmMeta v <- [ePayload edge]
        ]

    checkMetaVar v = do
      if v `elem` tmvars
        then checkType doc tt tyvars tmvars tmCtx (tmvSort v)
        else Left "validateDoctrine: unknown term variable"

checkParamTele :: Doctrine -> TypeTheory -> Text -> [GenParam] -> Either Text ()
checkParamTele doc tt label params = do
  teleDistinctNames params
  go [] [] params
  where
    go _ _ [] = Right ()
    go tyAcc tmAcc (param:rest) =
      case param of
        GP_Ty v -> do
          if M.member (tmVarOwner v) (mtModes (dModes doc))
            then Right ()
            else Left (label <> ": type parameter has unknown owner mode")
          if S.null (boundTmIndicesObj (tmvSort v))
            then Right ()
            else Left (label <> ": type parameter sort contains bound term indices")
          go (tyAcc <> [v]) tmAcc rest
        GP_Tm v -> do
          if S.null (boundTmIndicesObj (tmvSort v))
            then Right ()
            else Left (label <> ": term parameter sort contains bound term indices")
          checkType doc tt tyAcc tmAcc [] (tmvSort v)
          go tyAcc (tmAcc <> [v]) rest

checkGenLiteralKind :: Doctrine -> CtorTables -> GenDecl -> Either Text ()
checkGenLiteralKind doc ctorTables gd =
  case gdLiteralKind gd of
    Nothing -> Right ()
    Just _ ->
      if null (gdParams gd) && null (gdDom gd) && not (null eligibleOwners)
        then Right ()
        else Left ("validateDoctrine: invalid gdLiteralKind on generator " <> renderGen (gdName gd))
  where
    eligibleOwners =
      [ ownerMode
      | (ownerMode, table) <- M.toList ctorTables
      , let GenName genText = gdName gd
      , M.member (ObjName genText) table
      , Just decl <- [classifierOfMode (dModes doc) ownerMode]
      , cdClassifier decl == gdMode gd
      ]

checkAction :: Doctrine -> TypeTheory -> CtorTables -> (ModName, ModAction) -> Either Text ()
checkAction doc tt ctorTables (name, action) = do
  if maMod action == name
    then Right ()
    else Left "validateDoctrine: action declaration name mismatch"
  decl <-
    case M.lookup name (mtDecls (dModes doc)) of
      Nothing -> Left "validateDoctrine: action references unknown modality"
      Just d -> Right d
  let srcMode = mdSrc decl
  let tgtMode = mdTgt decl
  mapM_ (checkExplicitEntry srcMode tgtMode) (M.toList (maGenMap action))
  let srcGens =
        M.filterWithKey
          ( \gName _ ->
              not
                ( isTypeDeclGenNameInTables
                    doc
                    ctorTables
                    srcMode
                    (ObjName (renderGen gName))
                )
          )
          (M.findWithDefault M.empty srcMode (dGens doc))
  let checkGenImage g = do
        img <- actionImageForGenerator tt doc name g
        if dMode img == tgtMode
          then Right ()
          else Left "validateDoctrine: action generator image has wrong mode"
        validateDiagram img
  mapM_ checkGenImage (M.keys srcGens)
  where
    checkExplicitEntry srcMode tgtMode ((srcMode', g), img) = do
      if srcMode' == srcMode
        then Right ()
        else Left "validateDoctrine: action image key mode mismatch"
      _ <- lookupGenDeclInDoctrine "validateDoctrine: action references unknown source generator" doc srcMode g
      if dMode img == tgtMode
        then Right ()
        else Left "validateDoctrine: action generator image has wrong mode"
      validateDiagram img

actionImageForGenerator :: TypeTheory -> Doctrine -> ModName -> GenName -> Either Text Diagram
actionImageForGenerator tt doc modName genName = do
  modDecl <-
    case M.lookup modName (mtDecls (dModes doc)) of
      Nothing -> Left "action: unknown modality"
      Just decl -> Right decl
  let srcMode = mdSrc modDecl
  srcGen <- lookupGenDeclInDoctrine "action: unknown source generator" doc srcMode genName
  case M.lookup modName (dActions doc) >>= M.lookup (srcMode, genName) . maGenMap of
    Just img -> Right img
    Nothing -> canonicalActionImage tt doc modDecl srcGen

canonicalActionImage :: TypeTheory -> Doctrine -> ModDecl -> GenDecl -> Either Text Diagram
canonicalActionImage tt doc modDecl srcGen = do
  let tgtMode = mdTgt modDecl
  let genName = gdName srcGen
  tgtGen <-
    lookupGenDeclInDoctrine
      "action: missing generator image and no canonical same-name target generator"
      doc
      tgtMode
      genName
  ensureCanonicalActionFallbackCompatible tt doc modDecl srcGen tgtGen
  genericGenDiagram tgtGen

ensureCanonicalActionFallbackCompatible
  :: TypeTheory
  -> Doctrine
  -> ModDecl
  -> GenDecl
  -> GenDecl
  -> Either Text ()
ensureCanonicalActionFallbackCompatible tt doc modDecl srcGen tgtGen = do
  (targetTySubst, targetTyFlex) <- freshenTargetTyVars
  codeLift <- classifierLiftForModExpr (dModes doc) me
  domSection <- mkSection targetTySubst "domain" (mapSourceObj codeLift) (gdPlainDom srcGen) (gdPlainDom tgtGen)
  codSection <- mkSection targetTySubst "codomain" (mapSourceObj codeLift) (gdCod srcGen) (gdCod tgtGen)
  let srcBinders = [ bs | InBinder bs <- gdDom srcGen ]
  let tgtBinders = [ bs | InBinder bs <- gdDom tgtGen ]
  binderSections <-
    if length srcBinders == length tgtBinders
      then fmap concat (mapM (uncurry (mkBinderSections targetTySubst codeLift)) (zip [0 :: Int ..] (zip srcBinders tgtBinders)))
      else mismatch "binder arity mismatch"
  let allSections = domSection : codSection : binderSections
  _ <- foldM (unifySection targetTyFlex) emptySubst allSections
  Right ()
  where
    srcMode = mdSrc modDecl
    tgtMode = mdTgt modDecl
    me = ModExpr { meSrc = srcMode, meTgt = tgtMode, mePath = [mdName modDecl] }
    label =
      "action: canonical fallback for modality "
        <> renderModName (mdName modDecl)
        <> " generator "
        <> renderGen (gdName srcGen)

    mismatch detail =
      Left (label <> ": " <> detail <> "; provide an explicit action image")

    mkSection targetTySubst section mapObj srcCtx tgtCtx =
      if length srcCtx == length tgtCtx
        then do
          mapped <- mapM mapObj srcCtx
          tgtCtx' <- applySubstCtx tt targetTySubst tgtCtx
          pure (section, mapped, tgtCtx')
        else mismatch (section <> " arity mismatch")

    mkBinderSections targetTySubst codeLift i (srcBs, tgtBs) = do
      tmctx <- mkSection targetTySubst ("binder[" <> T.pack (show i) <> "].tmctx") (mapSourceTmCtxObj codeLift) (bsTmCtx srcBs) (bsTmCtx tgtBs)
      dom <- mkSection targetTySubst ("binder[" <> T.pack (show i) <> "].dom") (mapSourceObj codeLift) (bsDom srcBs) (bsDom tgtBs)
      cod <- mkSection targetTySubst ("binder[" <> T.pack (show i) <> "].cod") (mapSourceObj codeLift) (bsCod srcBs) (bsCod tgtBs)
      pure [tmctx, dom, cod]

    unifySection :: S.Set TmVar -> Subst -> (Text, Context, Context) -> Either Text Subst
    unifySection targetTyFlex subst (section, mappedSrc, tgtCtx) = do
      let flex = S.union targetTyFlex (S.fromList (gdTmVars tgtGen))
      mappedSrc' <- applySubstCtx tt subst mappedSrc
      tgtCtx' <- applySubstCtx tt subst tgtCtx
      solved <-
        case unifyCtx tt [] flex tgtCtx' mappedSrc' of
          Left _ -> mismatch (section <> " type mismatch")
          Right s -> Right s
      composeSubst tt solved subst

    mapSourceObj codeLift srcTy =
      if objOwnerMode srcTy == srcMode
        then
          pure
            Obj
              { objOwnerMode = tgtMode
              , objCode = CTLift codeLift (objCode srcTy)
              }
        else Left "action: source generator contains non-source-mode boundary object"

    mapSourceTmCtxObj codeLift srcTy =
      if objOwnerMode srcTy == srcMode
        then mapSourceObj codeLift srcTy
        else Right srcTy

    freshenTargetTyVars = do
      let tgtTyVars = gdTyVars tgtGen
      if null tgtTyVars
        then Right (emptySubst, S.empty)
        else do
          let used0 =
                S.fromList
                  [ (tyVarOwnerMode v, tmvName v)
                  | v <- gdTyVars srcGen <> tgtTyVars
                  ]
          let (_, pairsRev) = foldl freshOne (used0, []) tgtTyVars
          let pairs = reverse pairsRev
          subst <- mkSubst [ (old, CAObj (OVar new)) | (old, new) <- pairs ]
          pure (subst, S.fromList (map snd pairs))
      where
        freshOne (used, acc) v =
          let base = tmvName v <> "_tgt"
              mode = tyVarOwnerMode v
              name' = pickFresh used mode base (0 :: Int)
              v' = v { tmvName = name' }
              used' = S.insert (mode, name') used
           in (used', (v, v') : acc)

        pickFresh used mode base n =
          let suffix = if n == (0 :: Int) then "" else T.pack (show n)
              candidate = base <> suffix
           in if (mode, candidate) `S.member` used
                then pickFresh used mode base (n + 1)
                else candidate

    renderModName (ModName n) = n

genericGenDiagram :: GenDecl -> Either Text Diagram
genericGenDiagram gd = do
  let mode = gdMode gd
  args <- mapM mkParamArg (gdParams gd)
  let binderSlots = [ bs | InBinder bs <- gdDom gd ]
  let bargs = map BAMeta (binderHoleNames (length binderSlots))
  let (ins, d0) = allocPorts (gdPlainDom gd) (emptyDiagram mode [])
  let (outs, d1) = allocPorts (gdCod gd) d0
  d2 <- addEdgePayload (PGen (gdName gd) args bargs) ins outs d1
  let d3 = d2 { dIn = ins, dOut = outs }
  validateDiagram d3
  pure d3
  where
    mkParamArg param =
      case param of
        GP_Ty v -> Right (CAObj (OVar v))
        GP_Tm v -> CATm <$> tmVarDiagram v

    tmVarDiagram v = do
      let ownerMode = objOwnerMode (tmvSort v)
      let (outPid, d0) = freshPort (tmvSort v) (emptyDiagram ownerMode [])
      d1 <- addEdgePayload (PTmMeta v) [] [outPid] d0
      let d2 = d1 { dOut = [outPid] }
      validateDiagram d2
      pure (TermDiagram d2)

    binderHoleNames n =
      [ BinderMetaVar ("b" <> T.pack (show i))
      | i <- [0 :: Int .. n - 1]
      ]

instantiateGenParams :: TypeTheory -> GenDecl -> [CodeArg] -> Either Text Subst
instantiateGenParams tt gd args
  | length args /= length (gdParams gd) =
      Left "instantiateGenParams: generator argument arity mismatch"
  | otherwise =
      foldM step emptySubst (zip (gdParams gd) args)
  where
    step subst (param, arg) =
      case (param, arg) of
        (GP_Ty v, CAObj ty) ->
          bind v (CAObj ty) subst
        (GP_Tm v, CATm tm) -> do
          expectedSort <- applySubstObj tt subst (tmvSort v)
          actualSort <- termDiagramOutputSort "instantiateGenParams" (unTerm tm)
          let tmCtx = dTmCtx (unTerm tm)
          sortOk <- defEqObj tt tmCtx actualSort expectedSort
          if sortOk
            then bind v (CATm tm) subst
            else Left "instantiateGenParams: term argument sort mismatch"
        (GP_Ty _, CATm _) ->
          Left "instantiateGenParams: expected type argument"
        (GP_Tm _, CAObj _) ->
          Left "instantiateGenParams: expected term argument"

    bind v arg subst = do
      singleton <- mkSubst [(v, arg)]
      composeSubst tt singleton subst

applyModExprWithTypeTheory :: TypeTheory -> Doctrine -> ModExpr -> Diagram -> Either Text Diagram
applyModExprWithTypeTheory tt doc me diag = do
  if dMode diag /= meSrc me
    then Left "map: source mode mismatch"
    else Right ()
  case mePath me of
    [] ->
      if meSrc me == meTgt me
        then Right diag
        else Left "map: empty modality path has mismatched endpoints"
    mods -> do
      out <- foldM (\d m -> applyActionWithTypeTheory tt doc m d) diag mods
      if dMode out == meTgt me
        then Right out
        else Left "map: result mode mismatch"

applyActionWithTypeTheory :: TypeTheory -> Doctrine -> ModName -> Diagram -> Either Text Diagram
applyActionWithTypeTheory tt doc mName diagSrc = do
  decl <-
    case M.lookup mName (mtDecls (dModes doc)) of
      Nothing -> Left "map: unknown modality"
      Just d -> Right d
  if dMode diagSrc /= mdSrc decl
    then Left "map: modality source mismatch"
    else Right ()
  let me = ModExpr { meSrc = mdSrc decl, meTgt = mdTgt decl, mePath = [mName] }
  codeLift <- classifierLiftForModExpr (dModes doc) me
  let interp =
        DiagramInterpretation
          { diMapMode = \m ->
              if m == mdSrc decl then Right (mdTgt decl)
              else Left "map: modality source mismatch"
          , diMapTmCtxObj = mapTypeIfSource me codeLift
          , diMapPortObj = mapType me codeLift
          , diMapTmMetaSort = mapTypeIfSource me codeLift
          , diMapSplice = \x me0 -> do
              if meTgt me0 == mdSrc decl
                then Right ()
                else Left "map: splice modality context target mismatch"
              let composed =
                    ModExpr
                      { meSrc = meSrc me0
                      , meTgt = mdTgt decl
                      , mePath = mePath me0 <> [mName]
                      }
                  normalized = normalizeModExpr (dModes doc) composed
              if meSrc normalized == meSrc me0 && meTgt normalized == mdTgt decl
                then Right (x, normalized)
                else Left "map: splice modality context normalization changed endpoints"
          , diOnGenEdge = onGenEdge mName me codeLift
          }
  interpretDiagram interp diagSrc
  where
    stableCaptureRenaming =
      stableHoleCaptureRenaming
        (binderHoleCaptureRiskMetasDiagram diagSrc)
        (binderArgMetaVarsDiagram diagSrc)

    mapType me codeLift = mapTypeWithLift (dModes doc) me codeLift

    mapTypeIfSource me codeLift ty =
      if objOwnerMode ty == meSrc me
        then mapType me codeLift ty
        else Right ty

    onGenEdge modName me codeLift diagSrc0 diagTgt edgeKey edgeSrc mappedBargs =
      case ePayload edgeSrc of
        PGen g args _ -> do
          genDecl0 <- lookupGenDeclInDoctrine "map: unknown source generator" doc (dMode diagSrc0) g
          img0raw <- actionImageForGenerator tt doc modName g
          (genDecl, img0base) <- freshenGenDeclAndImage edgeKey genDecl0 img0raw
          let protectedVars = S.fromList (gdTyVars genDecl <> gdTmVars genDecl)
          (img0, renameSubst) <- freshenImageTyVars protectedVars diagTgt img0base
          argSubst <- instantiateGenParams tt genDecl args
          img1 <- applySubstDiagram tt argSubst img0
          (img2, subst) <-
            firstText
              (\err -> "map: generator " <> renderGen g <> " boundary instantiation failed: " <> err)
              (instantiateImage tt diagTgt edgeKey img1)
          img3 <-
            firstText
              (\err -> "map: generator " <> renderGen g <> " binder instantiation failed: " <> err)
              (instantiateMappedBinders me codeLift genDecl mappedBargs renameSubst subst img2)
          img4 <- weakenDiagramTmCtxTo (dTmCtx diagTgt) img3
          diagTgtNorm <- normalizeBoundaryPorts (eIns edgeSrc <> eOuts edgeSrc) diagTgt
          img4Norm <- normalizeDiagramObjExprs (dModes doc) img4
          spliceEdge diagTgtNorm edgeKey img4Norm
        _ ->
          Left "map: internal error: diOnGenEdge called on non-PGen"

    freshenGenDeclAndImage edgeIdx genDecl image0 = do
      (freshParams, renameSubst) <- freshenSourceParams edgeIdx (gdParams genDecl)
      domFresh <- mapM (renameInputShape renameSubst) (gdDom genDecl)
      codFresh <- applySubstCtx tt renameSubst (gdCod genDecl)
      imageFresh <- applySubstDiagram tt renameSubst image0
      pure
        ( genDecl
            { gdParams = freshParams
            , gdDom = domFresh
            , gdCod = codFresh
            }
        , imageFresh
        )

    freshenSourceParams edgeIdx =
      go 0 emptySubst []
      where
        go _ subst acc [] =
          Right (reverse acc, subst)
        go i subst acc (param : rest) =
          case param of
            GP_Ty v -> do
              sort' <- applySubstObj tt subst (tmvSort v)
              let fresh = freshTyParamVar edgeIdx i v sort'
              singleton <- mkSubst [(v, CAObj (OVar fresh))]
              subst' <- composeSubst tt singleton subst
              go (i + 1) subst' (GP_Ty fresh : acc) rest
            GP_Tm v -> do
              sort' <- applySubstObj tt subst (tmvSort v)
              let fresh = freshTmParamVar edgeIdx i v sort'
              tmFresh <- termExprToDiagramChecked tt [] sort' (TMMeta fresh [])
              singleton <- mkSubst [(v, CATm tmFresh)]
              subst' <- composeSubst tt singleton subst
              go (i + 1) subst' (GP_Tm fresh : acc) rest

    renameInputShape subst shape =
      case shape of
        InPort ty -> InPort <$> applySubstObj tt subst ty
        InBinder sig -> InBinder <$> applySubstBinderSig tt subst sig

    freshTyParamVar edgeIdx i v sort' =
      v
        { tmvName = tmvName v <> "__map" <> T.pack (show edgeIdx) <> "_" <> T.pack (show i)
        , tmvSort = sort'
        }

    freshTmParamVar edgeIdx i v sort' =
      v
        { tmvName = tmvName v <> "__map" <> T.pack (show edgeIdx) <> "_" <> T.pack (show i)
        , tmvSort = sort'
        , tmvOwnerMode = Nothing
        }

    instantiateMappedBinders me codeLift genDecl mappedBargs renameSubst subst image = do
      let slots = [ bs | InBinder bs <- gdDom genDecl ]
      if length slots /= length mappedBargs
        then Left "map: source binder argument arity mismatch"
        else Right ()
      let holes = binderHoleNames (length slots)
          mappedBargs' = renameBinderArgMetas stableCaptureRenaming mappedBargs
      sigs0 <- mapM mapBinderSig (M.fromList (zip holes slots))
      sigs1 <- applySubstBinderSigs tt renameSubst sigs0
      sigs <- applySubstBinderSigs tt subst sigs1
      let holeSub = M.fromList (zip holes mappedBargs')
      out <- instantiateGenImageBindersWithMapper tt (applyModExprWithTypeTheory tt doc) sigs holeSub image
      let remaining = S.intersection (M.keysSet sigs) (binderMetaVarsDiagram out)
      if S.null remaining
        then Right out
        else Left "map: uninstantiated binder holes in action image"
      where
        mapBinderSig sig = do
          tmCtx <- mapM (mapTypeIfSource me codeLift) (bsTmCtx sig)
          dom <- mapM (mapType me codeLift) (bsDom sig)
          cod <- mapM (mapType me codeLift) (bsCod sig)
          pure sig { bsTmCtx = tmCtx, bsDom = dom, bsCod = cod }

    freshenImageTyVars protected host image = do
      let vars = S.toList (S.difference (freeVarsDiagram image) protected)
      if null vars
        then do
          subst <- mkSubst []
          pure (image, subst)
        else do
          let used0 = S.fromList [ (tmVarOwner v, tmvName v) | v <- S.toList (freeVarsDiagram host) ]
              (_, pairsRev) = foldl freshOne (used0, []) vars
          subst <- mkSubst [ (v, CAObj (OVar v')) | (v, v') <- reverse pairsRev ]
          image' <- applySubstDiagram tt subst image
          pure (image', subst)
      where
        freshOne (used, acc) v =
          let name' = pickFresh used (tyVarMode v) (tmvName v <> "_img") 0
              v' = v { tmvName = name' }
              used' = S.insert (tmVarOwner v', tmvName v') used
           in (used', (v, v') : acc)

    tyVarMode v =
      case tmvOwnerMode v of
        Just owner -> owner
        Nothing -> objOwnerMode (tmvSort v)

    pickFresh used mode base n =
      let suffix = if n == (0 :: Int) then "" else T.pack (show n)
          candidate = base <> suffix
       in if (mode, candidate) `S.member` used
            then pickFresh used mode base (n + 1)
            else candidate

    normalizeBoundaryPorts pids diag = do
      portObj' <- foldM normalizeOne (dPortObj diag) pids
      pure diag { dPortObj = portObj' }
      where
        normalizeOne mp pid =
          case IM.lookup (unPortId pid) mp of
            Nothing -> Left "map: missing boundary port while normalizing action image splice"
            Just ty -> do
              ty' <- normalizeObjExpr (dModes doc) ty
              pure (IM.insert (unPortId pid) ty' mp)

instantiateImage :: TypeTheory -> Diagram -> Int -> Diagram -> Either Text (Diagram, Subst)
instantiateImage tt diag edgeKey img = do
  edge <-
    case IM.lookup edgeKey (dEdges diag) of
      Nothing -> Left "map: missing target edge"
      Just e -> Right e
  domEdge <- mapM (requirePortType "map" diag) (eIns edge)
  codEdge <- mapM (requirePortType "map" diag) (eOuts edge)
  domImg <- diagramDom img
  codImg <- diagramCod img
  let flex = freeVarsDiagram img
  sDom <- unifyCtxDiagram tt diag flex domImg domEdge
  codImg1 <- applySubstCtx tt sDom codImg
  codEdge1 <- applySubstCtx tt sDom codEdge
  sCod <- unifyCtxDiagram tt diag flex codImg1 codEdge1
  s <- composeSubst tt sCod sDom
  img' <- applySubstDiagram tt s img
  imgNorm <- normalizeDiagramObjExprs (ttModes tt) img'
  pure (imgNorm, s)

normalizeDiagramObjExprs :: ModeTheory -> Diagram -> Either Text Diagram
normalizeDiagramObjExprs mt diag = do
  portObj' <- mapM (normalizeObjExpr mt) (dPortObj diag)
  tmCtx' <- mapM (normalizeObjExpr mt) (dTmCtx diag)
  edges' <- mapM normalizeEdge (dEdges diag)
  pure diag { dPortObj = portObj', dTmCtx = tmCtx', dEdges = edges' }
  where
    normalizeEdge edge = do
      payload' <- normalizePayload (ePayload edge)
      pure edge { ePayload = payload' }

    normalizePayload payload =
      case payload of
        PGen g args bargs ->
          PGen g args <$> mapM normalizeBinderArg bargs
        PProvider ref ->
          pure (PProvider ref)
        PModuleRef ref ->
          pure (PModuleRef ref)
        PBox name inner ->
          PBox name <$> normalizeDiagramObjExprs mt inner
        PFeedback inner ->
          PFeedback <$> normalizeDiagramObjExprs mt inner
        PTmMeta v -> do
          sort' <- normalizeObjExpr mt (tmvSort v)
          pure (PTmMeta v { tmvSort = sort' })
        PSplice x me ->
          pure (PSplice x me)
        PInternalDrop ->
          pure PInternalDrop

    normalizeBinderArg barg =
      case barg of
        BAConcrete inner ->
          BAConcrete <$> normalizeDiagramObjExprs mt inner
        BAMeta v ->
          pure (BAMeta v)

mapTypeWithLift :: ModeTheory -> ModExpr -> ModExpr -> Obj -> Either Text Obj
mapTypeWithLift mt me codeLift ty = do
  if objOwnerMode ty /= meSrc me
    then Left "map: type mode does not match action source"
    else
      normalizeObjExpr
        mt
        Obj
          { objOwnerMode = meTgt me
          , objCode = CTLift codeLift (objCode ty)
          }

firstText :: (Text -> Text) -> Either Text a -> Either Text a
firstText = first

checkModeTransform :: Doctrine -> ModTransformDecl -> Either Text ()
checkModeTransform doc decl = do
  let witnessMode = meTgt (mtdFrom decl)
  witnessGen <-
    case M.lookup witnessMode (dGens doc) >>= M.lookup (mtdWitness decl) of
      Nothing -> Left "validateDoctrine: modality transform witness references unknown generator"
      Just gen -> Right gen
  checkModTransformWitness doc (mtdFrom decl) (mtdTo decl) witnessGen

checkObligation :: Doctrine -> TypeTheory -> ObligationDecl -> Either Text ()
checkObligation doc tt obl = do
  checkParamTele doc tt ("validateDoctrine: obligation " <> obName obl) (obParams obl)
  if obForGen obl
    then do
      case obForGenName obl of
        Nothing -> Right ()
        Just targetGen ->
          case M.lookup (obMode obl) (dGens doc) >>= M.lookup targetGen of
            Nothing ->
              Left
                ( "validateDoctrine: obligation "
                    <> obName obl
                    <> " references unknown generator "
                    <> renderMode (obMode obl)
                    <> "."
                    <> renderGen targetGen
                )
            Just _ -> Right ()
      if null (obTyVars obl) && null (obTmVars obl) && null (obDom obl) && null (obCod obl)
        then Right ()
        else Left "validateDoctrine: for_gen obligation must not declare vars or boundary signature"
      ensureNoGenRefs False (obLHSExpr obl)
      ensureNoGenRefs False (obRHSExpr obl)
    else do
      case obForGenName obl of
        Nothing -> Right ()
        Just _ ->
          Left "validateDoctrine: obligation target generator requires for_gen"
      checkContext doc tt (obMode obl) (obTyVars obl) (obTmVars obl) [] (obDom obl)
      checkContext doc tt (obMode obl) (obTyVars obl) (obTmVars obl) [] (obCod obl)
      ensureNoGenRefs True (obLHSExpr obl)
      ensureNoGenRefs True (obRHSExpr obl)
  where
    ensureNoGenRefs allow expr =
      case expr of
        ROEDiag _ -> Right ()
        ROEMap _ inner -> ensureNoGenRefs allow inner
        ROEGen ->
          if allow
            then Left "validateDoctrine: @gen is only allowed in for_gen obligations"
            else Right ()
        ROELiftDom _
          | allow -> Left "validateDoctrine: lift_dom is only allowed in for_gen obligations"
          | otherwise -> Right ()
        ROELiftCod _
          | allow -> Left "validateDoctrine: lift_cod is only allowed in for_gen obligations"
          | otherwise -> Right ()
        ROEComp a b -> ensureNoGenRefs allow a >> ensureNoGenRefs allow b
        ROETensor a b -> ensureNoGenRefs allow a >> ensureNoGenRefs allow b

checkModTransformWitness :: Doctrine -> ModExpr -> ModExpr -> GenDecl -> Either Text ()
checkModTransformWitness doc fromMe toMe witness = do
  let witnessMode = meTgt fromMe
  if gdMode witness == witnessMode
    then Right ()
    else Left "mod_transform: witness generator is declared in the wrong mode"
  tyVar <-
    case gdTyVars witness of
      [v] -> Right v
      _ -> Left "mod_transform: witness generator must have exactly one type variable"
  if tyVarOwnerMode tyVar == meSrc fromMe
    then Right ()
    else Left "mod_transform: witness type variable must live in transform source mode"
  if null (gdTmVars witness)
    then Right ()
    else Left "mod_transform: witness generator must not have term variables"
  domTy <-
    case gdDom witness of
      [InPort ty] -> Right ty
      _ -> Left "mod_transform: witness generator domain must be exactly one input port"
  codTy <-
    case gdCod witness of
      [ty] -> Right ty
      _ -> Left "mod_transform: witness generator codomain must be exactly one output port"
  expectedDom <- mapOwnerModalType fromMe (OVar tyVar)
  expectedCod <- mapOwnerModalType toMe (OVar tyVar)
  domNorm <- normalizeObjExpr (dModes doc) domTy
  codNorm <- normalizeObjExpr (dModes doc) codTy
  expectedDomNorm <- normalizeObjExpr (dModes doc) expectedDom
  expectedCodNorm <- normalizeObjExpr (dModes doc) expectedCod
  if domNorm == expectedDomNorm && codNorm == expectedCodNorm
    then Right ()
    else Left "mod_transform: witness generator must have type [mu(A)] -> [nu(A)] for the declared transform"
  where
    mapOwnerModalType me ty = do
      codeLift <- classifierLiftForModExpr (dModes doc) me
      pure
        Obj
          { objOwnerMode = meTgt me
          , objCode = CTLift codeLift (objCode ty)
          }

tyVarOwnerMode :: TmVar -> ModeName
tyVarOwnerMode v =
  case tmvOwnerMode v of
    Just owner -> owner
    Nothing -> objOwnerMode (tmvSort v)

renderGen :: GenName -> Text
renderGen (GenName t) = t

unObjName :: ObjName -> Text
unObjName (ObjName t) = t

renderMode :: ModeName -> Text
renderMode (ModeName t) = t
