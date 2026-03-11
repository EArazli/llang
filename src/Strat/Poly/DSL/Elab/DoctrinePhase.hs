{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.DSL.Elab.DoctrinePhase
  ( elabPolyDoctrine
  , elabPolyDoctrineWithBudget
  , elabPolyDoctrineWithBudgetResult
  , elabPolyDoctrineFromBaseWithBudgetResult
  , identityMorphismFor
  ) where

import Control.Monad (foldM)
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe)
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import Strat.Common.Rules (Orientation (..), RewritePolicy (..), RuleClass (..))
import Strat.Frontend.Env (ModuleEnv(..))
import Strat.Poly.BeckChevalleyObligations (installGeneratedBeckChevalleyObligations, isGeneratedBeckChevalleyObligation)
import Strat.Poly.Cell2 (Cell2(..))
import Strat.Poly.CompObligations (installGeneratedCompObligations, isGeneratedCompObligation)
import Strat.Poly.DSL.AST
import Strat.Poly.DSL.Elab.Build
  ( BuildOps(..)
  , ElabState(..)
  , applyPendingDeclarations
  , refreshPendingClassificationsBestEffort
  , seedDoctrine
  )
import Strat.Poly.DSL.Elab.Diag
  ( BinderMetaMode(..)
  , elabDiagExprWith
  , elabRuleLHS
  , elabRuleRHS
  , ensureAcyclicMode
  , ensureMode
  , lookupGen
  , mkForGenDiag
  , renderGenName
  , unifyBoundary
  )
import Strat.Poly.DSL.Elab.Implements
  ( ImplementsCheckResult(..)
  , checkImplementsObligationsWithBudget
  )
import Strat.Poly.DSL.Elab.PhaseTypes
  ( ClassificationDeclRaw(..)
  , UniverseSpec(..)
  )
import Strat.Poly.DSL.Elab.Resolve
  ( elabRawModExpr
  , unresolvedClassUniverse
  )
import Strat.Poly.DSL.Elab.Term
  ( elabContext
  , elabInputShapes
  , elabObjExprWithTables
  , elabParamDecls
  , provisionalCtorSort
  )
import Strat.Poly.Diagram
import Strat.Poly.DiagramInterpretation (binderHoleNames)
import Strat.Poly.Doctrine
import Strat.Poly.Graph (BinderMetaVar(..))
import Strat.Poly.ModeTheory
import Strat.Poly.ModAction (ActionSemanticsResult(..), mapTypeByModExprWithLift, validateActionSemanticsWithBudgetResult)
import Strat.Poly.Morphism
import Strat.Poly.Names
import Strat.Poly.Obj
import Strat.Poly.ObjClassifier (modeClassifierMode, modeUniverseObj)
import Strat.Poly.Proof
  ( SearchBudget(..)
  , defaultSearchBudget
  , renderSearchLimit
  )

elabPolyDoctrine :: ModuleEnv -> RawPolyDoctrine -> Either Text Doctrine
elabPolyDoctrine env raw = fst <$> elabPolyDoctrineWithBudgetResult defaultSearchBudget env raw

elabPolyDoctrineWithBudget :: SearchBudget -> ModuleEnv -> RawPolyDoctrine -> Either Text Doctrine
elabPolyDoctrineWithBudget budget env raw =
  fst <$> elabPolyDoctrineWithBudgetResult budget env raw

elabPolyDoctrineWithBudgetResult :: SearchBudget -> ModuleEnv -> RawPolyDoctrine -> Either Text (Doctrine, Int)
elabPolyDoctrineWithBudgetResult budget env raw = do
  base <- case rpdExtends raw of
    Nothing -> Right Nothing
    Just name ->
      case M.lookup name (meDoctrines env) of
        Nothing -> Left ("Unknown doctrine: " <> name)
        Just doc -> Right (Just doc)
  let start =
        ElabState
          { esDoc = seedDoctrine (rpdName raw) base
          , esPendingClass = []
          , esPendingComp = []
          }
  st <- foldM (elabPolyItemWithRefresh env) start (rpdItems raw)
  doc0 <- applyPendingDeclarations buildOps st
  docComp <- installGeneratedCompObligations doc0
  doc <- installGeneratedBeckChevalleyObligations docComp
  validateDoctrine doc
  actionProofCount <- validateActionSemanticsProofCount budget doc
  compProofCount <- validateCompSemanticsProofCount budget env doc
  bcProofCount <- validateBCSemanticsProofCount budget env doc
  pure (doc, actionProofCount + compProofCount + bcProofCount)

elabPolyDoctrineFromBaseWithBudgetResult
  :: SearchBudget
  -> ModuleEnv
  -> Doctrine
  -> RawPolyDoctrine
  -> Either Text (Doctrine, Int)
elabPolyDoctrineFromBaseWithBudgetResult budget env baseDoc raw = do
  let start =
        ElabState
          { esDoc = seedDoctrine (rpdName raw) (Just baseDoc)
          , esPendingClass = []
          , esPendingComp = []
          }
  st <- foldM (elabPolyItemWithRefresh env) start (rpdItems raw)
  doc0 <- applyPendingDeclarations buildOps st
  docComp <- installGeneratedCompObligations doc0
  doc <- installGeneratedBeckChevalleyObligations docComp
  validateDoctrine doc
  actionProofCount <- validateActionSemanticsProofCount budget doc
  compProofCount <- validateCompSemanticsProofCount budget env doc
  bcProofCount <- validateBCSemanticsProofCount budget env doc
  pure (doc, actionProofCount + compProofCount + bcProofCount)

validateActionSemanticsProofCount :: SearchBudget -> Doctrine -> Either Text Int
validateActionSemanticsProofCount budget doc = do
  result <- validateActionSemanticsWithBudgetResult budget doc
  case result of
    ActionSemanticsProved proofs ->
      Right (length proofs)
    ActionSemanticsUndecided label lim ->
      Left
        ( "validateDoctrine: action semantics undecided for "
            <> label
            <> " ("
            <> renderSearchLimit lim
            <> ")"
        )

validateCompSemanticsProofCount :: SearchBudget -> ModuleEnv -> Doctrine -> Either Text Int
validateCompSemanticsProofCount budget env doc = do
  let generated = [obl | obl <- dObligations doc, isGeneratedCompObligation obl]
  if null generated
    then Right 0
    else do
      let schemaDoc = doc { dObligations = generated }
      identityMor <- identityMorphismFor doc
      result <- checkImplementsObligationsWithBudget budget env doc identityMor schemaDoc
      case result of
        ImplementsCheckProved proofs ->
          Right (length proofs)
        ImplementsCheckUndecided label lim ->
          Left
            ( "validateDoctrine: comprehension semantics undecided for "
                <> label
                <> " ("
                <> renderSearchLimit lim
                <> ")"
            )

validateBCSemanticsProofCount :: SearchBudget -> ModuleEnv -> Doctrine -> Either Text Int
validateBCSemanticsProofCount budget env doc = do
  let generated = [obl | obl <- dObligations doc, isGeneratedBeckChevalleyObligation obl]
  if null generated
    then Right 0
    else do
      let schemaDoc = doc { dObligations = generated }
      identityMor <- identityMorphismFor doc
      result <- checkImplementsObligationsWithBudget budget env doc identityMor schemaDoc
      case result of
        ImplementsCheckProved proofs ->
          Right (length proofs)
        ImplementsCheckUndecided label lim ->
          Left
            ( "validateDoctrine: Beck-Chevalley semantics undecided for "
                <> label
                <> " ("
                <> renderSearchLimit lim
                <> ")"
            )

identityMorphismFor :: Doctrine -> Either Text Morphism
identityMorphismFor doc = do
  genMap <- mkIdentityGenMap doc
  pure
    Morphism
      { morName = "__generated.comp.identity"
      , morSrc = doc
      , morTgt = doc
      , morIsCoercion = True
      , morModeMap = modeMap
      , morModMap = modMap
      , morTypeMap = M.empty
      , morGenMap = genMap
      , morCheck = CheckNone
      , morPolicy = UseStructuralAsBidirectional
      }
  where
    modeMap =
      M.fromList
        [ (m, m)
        | m <- M.keys (mtModes (dModes doc))
        ]
    modMap =
      M.fromList
        [ ( name
          , ModExpr
              { meSrc = mdSrc decl
              , meTgt = mdTgt decl
              , mePath = [name]
              }
          )
        | (name, decl) <- M.toList (mtDecls (dModes doc))
        ]
mkIdentityGenMap :: Doctrine -> Either Text (M.Map (ModeName, GenName) GenImage)
mkIdentityGenMap doc = do
  ctorTables <- deriveCtorTables doc
  fmap M.fromList (mapM mkOne (allNonTypeGens ctorTables))
  where
    allNonTypeGens ctorTables =
      [ (mode, gd)
      | (mode, table) <- M.toList (dGens doc)
      , gd <- M.elems table
      , not (isTypeDeclGenNameInTables doc ctorTables mode (ObjName (renderGenName (gdName gd))))
      ]

    mkOne (mode, gd) = do
      diag <- mkForGenDiag mode gd
      let binderSlots = [ bs | InBinder bs <- gdDom gd ]
      let holes = [ BinderMetaVar ("for_gen_b" <> T.pack (show i)) | i <- [0 .. length binderSlots - 1] ]
      let binderSigs = M.fromList (zip holes binderSlots)
      pure ((mode, gdName gd), GenImage diag binderSigs)

buildOps :: BuildOps
buildOps =
  BuildOps
    { boResolveSeedUniverse = unresolvedClassUniverse
    , boElabUniverseWithTables =
        \doc ctorTables classifier rawUniverse ->
          elabObjExprWithTables doc ctorTables [] [] M.empty classifier rawUniverse
    }

elabPolyItemWithRefresh :: ModuleEnv -> ElabState -> RawPolyItem -> Either Text ElabState
elabPolyItemWithRefresh env st item =
  elabPolyItem env (refreshPendingClassificationsBestEffort buildOps st) item

elabPolyItem :: ModuleEnv -> ElabState -> RawPolyItem -> Either Text ElabState
elabPolyItem env st item =
  let doc = esDoc st
   in
  case item of
    RPMode decl -> do
      let mode = ModeName (rmdName decl)
      mtAdded <- addMode mode (dModes doc)
      mt0 <-
        case rmdDefEqEngine decl of
          Nothing -> Right mtAdded
          Just RDETRS -> setModeDefEqEngine mode DefEqTRS mtAdded
          Just RDENBE -> setModeDefEqEngine mode DefEqNBE mtAdded
      mt' <-
        case rmdClassifiedBy decl of
          Nothing -> Right mt0
          Just rawClass -> do
            let classifier = ModeName (rcdClassifier rawClass)
            seedUniverse <- unresolvedClassUniverse (doc { dModes = mt0 }) classifier (rcdUniverse rawClass)
            addClassification
              mode
              ClassificationDecl
                { cdClassifier = classifier
                , cdUniverse = seedUniverse
                , cdComp = Nothing
                }
              mt0
      let acyclic' =
            if rmdAcyclic decl
              then S.insert mode (dAcyclicModes doc)
              else dAcyclicModes doc
      let pending' =
            case rmdClassifiedBy decl of
              Nothing -> esPendingClass st
              Just rawClass ->
                esPendingClass st
                  <> [ ( mode
                       , ClassificationDeclRaw
                           { cdrClassifier = ModeName (rcdClassifier rawClass)
                           , cdrUniverse = UniverseRaw (rcdUniverse rawClass)
                           }
                       )
                     ]
      pure
        st
          { esDoc = doc { dModes = mt', dAcyclicModes = acyclic' }
          , esPendingClass = pending'
          }
    RPComprehension compDecl ->
      pure st { esPendingComp = esPendingComp st <> [compDecl] }
    RPClassifierLift decl -> do
      let modName = ModName (rclModality decl)
      liftExpr <- elabRawModExpr (dModes doc) (rclLift decl)
      mt' <- addClassifierLift modName liftExpr (dModes doc)
      pure st { esDoc = doc { dModes = mt' } }
    RPModality decl -> do
      let modDecl =
            ModDecl
              { mdName = ModName (rmodName decl)
              , mdSrc = ModeName (rmodSrc decl)
              , mdTgt = ModeName (rmodTgt decl)
              }
      mt' <- addModDecl modDecl (dModes doc)
      pure st { esDoc = doc { dModes = mt' } }
    RPModEq decl -> do
      lhs <- elabRawModExpr (dModes doc) (rmeLHS decl)
      rhs <- elabRawModExpr (dModes doc) (rmeRHS decl)
      mt' <- addModEqn (ModEqn lhs rhs) (dModes doc)
      pure st { esDoc = doc { dModes = mt' } }
    RPModTransform decl ->
      do
        doc' <- elabModTransformDecl doc decl
        pure st { esDoc = doc' }
    RPAction decl -> do
      let modName = ModName (radModName decl)
      modDecl <-
        case M.lookup modName (mtDecls (dModes doc)) of
          Nothing -> Left "action references unknown modality"
          Just d -> Right d
      let srcMode = mdSrc modDecl
      let tgtMode = mdTgt modDecl
      imgs <- mapM (elabActionImage env doc modName srcMode tgtMode) (radGenMap decl)
      let action =
            ModAction
              { maMod = modName
              , maGenMap = M.fromList [ ((srcMode, g), d) | (g, d) <- imgs ]
              , maPolicy = UseStructuralAsBidirectional
              }
      if M.member modName (dActions doc)
        then Left "duplicate action declaration"
        else pure st { esDoc = doc { dActions = M.insert modName action (dActions doc) } }
    RPObligation decl -> do
      let mode = ModeName (rodMode decl)
      ensureMode doc mode
      if rodForGen decl
        then do
          if null (rodVars decl) && null (rodDom decl) && null (rodCod decl)
            then pure ()
            else Left "obligation for_gen does not accept explicit vars or boundary signature"
          validateObligationExprMode doc mode True (rodLHS decl)
          validateObligationExprMode doc mode True (rodRHS decl)
          let obl =
                ObligationDecl
                  { obName = rodName decl
                  , obMode = mode
                  , obForGen = True
                  , obForGenName = Nothing
                  , obGenerated = False
                  , obParams = []
                  , obDom = []
                  , obCod = []
                  , obLHSExpr = rodLHS decl
                  , obRHSExpr = rodRHS decl
                  , obPolicy = UseStructuralAsBidirectional
                  }
          pure st { esDoc = doc { dObligations = dObligations doc <> [obl] } }
        else do
          params <- elabParamDecls doc mode (rodVars decl)
          let tyVars = [ v | GP_Ty v <- params ]
          let tmVars = [ v | GP_Tm v <- params ]
          dom <- elabContext doc mode tyVars tmVars M.empty (rodDom decl)
          cod <- elabContext doc mode tyVars tmVars M.empty (rodCod decl)
          validateObligationExprMode doc mode False (rodLHS decl)
          validateObligationExprMode doc mode False (rodRHS decl)
          let obl =
                ObligationDecl
                  { obName = rodName decl
                  , obMode = mode
                  , obForGen = False
                  , obForGenName = Nothing
                  , obGenerated = False
                  , obParams = params
                  , obDom = dom
                  , obCod = cod
                  , obLHSExpr = rodLHS decl
                  , obRHSExpr = rodRHS decl
                  , obPolicy = UseStructuralAsBidirectional
                  }
          pure st { esDoc = doc { dObligations = dObligations doc <> [obl] } }
    RPLiteral decl -> do
      doc' <- installLiteralDecl doc decl
      pure st { esDoc = doc' }
    RPGen decl -> do
      let mode = ModeName (rpgMode decl)
      ensureMode doc mode
      let gname = GenName (rpgName decl)
      params <- elabParamDecls doc mode (rpgVars decl)
      let tyVars = [ v | GP_Ty v <- params ]
      let tmVars = [ v | GP_Tm v <- params ]
      let table0 = M.findWithDefault M.empty mode (dGens doc)
      if M.member gname table0
        then Left "duplicate generator name"
        else Right ()
      let provisional =
            GenDecl
              { gdName = gname
              , gdMode = mode
              , gdParams = params
              , gdDom = []
              , gdCod = [provisionalCtorSort doc mode]
              , gdLiteralKind = Nothing
              }
      let docForElab =
            doc
              { dGens = M.insert mode (M.insert gname provisional table0) (dGens doc)
              }
      dom <- elabInputShapes docForElab mode tyVars tmVars (rpgDom decl)
      cod <- elabContext docForElab mode tyVars tmVars M.empty (rpgCod decl)
      let gen = GenDecl
            { gdName = gname
            , gdMode = mode
            , gdParams = params
            , gdDom = dom
            , gdCod = cod
            , gdLiteralKind = Nothing
            }
      let table' = M.insert gname gen table0
      let gens' = M.insert mode table' (dGens doc)
      pure st { esDoc = doc { dGens = gens' } }
    RPData decl -> do
      let modeName = rpdTyMode decl
      let ownerMode = ModeName modeName
      ensureMode doc ownerMode
      let classifierMode = modeClassifierMode (dModes doc) ownerMode
      ensureMode doc classifierMode
      universe <-
        case modeUniverseObj (dModes doc) ownerMode of
          Nothing ->
            Left
              ( "data: mode "
                  <> modeName
                  <> " is missing a classifiedBy universe"
              )
          Just u -> Right u
      let ctorNames = map rpdCtorName (rpdCtors decl)
      ensureDistinct "data: duplicate constructor name" ctorNames
      let typeName = rpdTyName decl
      let existingOwner = M.findWithDefault M.empty ownerMode (dGens doc)
      let existingClassifier = M.findWithDefault M.empty classifierMode (dGens doc)
      case [c | c <- ctorNames, M.member (GenName c) existingOwner] of
        (c:_) -> Left ("data: constructor name conflicts with generator " <> c)
        [] -> Right ()
      if M.member (GenName typeName) existingClassifier
        then Left ("data: type constructor name conflicts with classifier generator " <> typeName)
        else Right ()
      params <- elabParamDecls doc classifierMode (map RPDType (rpdTyVars decl))
      let typeCtorGen =
            GenDecl
              { gdName = GenName typeName
              , gdMode = classifierMode
              , gdParams = params
              , gdDom = []
              , gdCod = [universe]
              , gdLiteralKind = Nothing
              }
      let classifierTable' = M.insert (gdName typeCtorGen) typeCtorGen existingClassifier
      let doc' =
            doc
              { dGens = M.insert classifierMode classifierTable' (dGens doc)
              }
      let st' = st { esDoc = doc' }
      let ctors = map (mkCtor modeName typeName (rpdTyVars decl)) (rpdCtors decl)
      let (foldGen, foldRules) =
            mkFoldBundle
              modeName
              typeName
              (rpdTyVars decl)
              (rpdCtors decl)
      let items =
            (map RPGen ctors)
              <> [RPGen foldGen]
              <> (map RPRule foldRules)
      foldM (elabPolyItemWithRefresh env) st' items
    RPRule decl -> do
      let mode = ModeName (rprMode decl)
      ensureMode doc mode
      if any ((== rprName decl) . c2Name) (dCells2 doc)
        then Left "duplicate rule name"
        else Right ()
      params <- elabParamDecls doc mode (rprVars decl)
      let ruleTyVars = [ v | GP_Ty v <- params ]
      let ruleTmVars = [ v | GP_Tm v <- params ]
      dom <- elabContext doc mode ruleTyVars ruleTmVars M.empty (rprDom decl)
      cod <- elabContext doc mode ruleTyVars ruleTmVars M.empty (rprCod decl)
      (lhs, binderSigs) <- withRule (elabRuleLHS env doc mode ruleTyVars ruleTmVars (rprLHS decl))
      rhs <- withRule (elabRuleRHS env doc mode ruleTyVars ruleTmVars binderSigs (rprRHS decl))
      let rigidTy = S.fromList ruleTyVars
      let rigidTm = S.fromList ruleTmVars
      tt <- doctrineTypeTheory doc
      lhs' <-
        case unifyBoundary tt rigidTy rigidTm dom cod lhs of
          Left err -> Left ("rule " <> rprName decl <> ": lhs boundary mismatch: " <> err)
          Right diag -> Right diag
      rhs' <-
        case unifyBoundary tt rigidTy rigidTm dom cod rhs of
          Left err -> Left ("rule " <> rprName decl <> ": rhs boundary mismatch: " <> err)
          Right diag -> Right diag
      let free = S.union (freeVarsDiagram lhs') (freeVarsDiagram rhs')
      let allowed = S.fromList (ruleTyVars <> ruleTmVars)
      if S.isSubsetOf free allowed
        then pure ()
        else Left ("rule " <> rprName decl <> ": unresolved metavariables")
      let cell = Cell2
            { c2Name = rprName decl
            , c2Class = rprClass decl
            , c2Orient = rprOrient decl
            , c2Params = params
            , c2LHS = lhs'
            , c2RHS = rhs'
            }
      pure st { esDoc = doc { dCells2 = dCells2 doc <> [cell] } }
      where
        withRule action =
          case action of
            Left err -> Left ("rule " <> rprName decl <> ": " <> err)
            Right x -> Right x

elabModTransformDecl :: Doctrine -> RawModTransformDecl -> Either Text Doctrine
elabModTransformDecl doc decl = do
  fromMe <- elabRawModExpr (dModes doc) (rmtFrom decl)
  toMe <- elabRawModExpr (dModes doc) (rmtTo decl)
  if meSrc fromMe == meSrc toMe && meTgt fromMe == meTgt toMe
    then Right ()
    else Left "mod_transform: source/target mismatch between transform sides"
  let witnessText = fromMaybe (rmtName decl) (rmtWitness decl)
  let witness = GenName witnessText
  let witnessMode = meTgt fromMe
  witnessGen <- lookupGen doc witnessMode witness
  checkModTransformWitness doc fromMe toMe witnessGen
  let transformDecl =
        ModTransformDecl
          { mtdName = ModTransformName (rmtName decl)
          , mtdFrom = fromMe
          , mtdTo = toMe
          , mtdWitness = witness
          }
  mt' <- addModTransformDecl transformDecl (dModes doc)
  pure doc { dModes = mt' }

ensureDistinct :: Text -> [Text] -> Either Text ()
ensureDistinct label names =
  let set = S.fromList names
  in if S.size set == length names then Right () else Left label

installLiteralDecl :: Doctrine -> RawLiteralDecl -> Either Text Doctrine
installLiteralDecl doc decl = do
  let ownerMode = ModeName (rldOwnerMode decl)
  ensureMode doc ownerMode
  universe <-
    case modeUniverseObj (dModes doc) ownerMode of
      Nothing -> Left "literal: owner mode is missing a classifiedBy universe"
      Just u -> Right u
  let classifierMode = modeClassifierMode (dModes doc) ownerMode
  let genName = GenName (rldTypeName decl)
  table <-
    case M.lookup classifierMode (dGens doc) of
      Nothing -> Left "literal: classifier mode has no generators"
      Just t -> Right t
  genDecl <-
    case M.lookup genName table of
      Nothing -> Left "literal: unknown type constructor"
      Just gd -> Right gd
  if gdParams genDecl == [] && gdDom genDecl == [] && gdCod genDecl == [universe]
    then Right ()
    else Left "literal: target must be a nullary type constructor for the owner mode"
  case gdLiteralKind genDecl of
    Nothing ->
      let genDecl' = genDecl { gdLiteralKind = Just (rldKind decl) }
          table' = M.insert genName genDecl' table
       in Right doc { dGens = M.insert classifierMode table' (dGens doc) }
    Just _ ->
      Left "literal: duplicate literal declaration"

rpdCtorName :: RawPolyCtorDecl -> Text
rpdCtorName = rpcName

mkCtor :: Text -> Text -> [RawTyVarDecl] -> RawPolyCtorDecl -> RawPolyGenDecl
mkCtor modeName tyName vars ctor =
  let typeRef = RawTypeRef { rtrMode = Nothing, rtrName = tyName }
      args = map (RPTVar . rtvName) vars
      cod = [RPTCon typeRef args]
  in RawPolyGenDecl
      { rpgName = rpcName ctor
      , rpgVars = map RPDType vars
      , rpgDom = map RIPort (rpcArgs ctor)
      , rpgCod = cod
      , rpgMode = modeName
      }

freshWithPrimes :: S.Set Text -> Text -> Text
freshWithPrimes used base =
  if base `S.member` used then freshWithPrimes used (base <> "'") else base

mkFoldBundle
  :: Text
  -> Text
  -> [RawTyVarDecl]
  -> [RawPolyCtorDecl]
  -> (RawPolyGenDecl, [RawPolyRuleDecl])
mkFoldBundle modeName tyName tyVars ctors =
  (foldGen, foldRules)
  where
    foldName = "fold_" <> tyName
    resTyBase = "r_" <> tyName
    resTyName = freshWithPrimes (S.fromList (map rtvName tyVars)) resTyBase
    resTyVarDecl =
      RawTyVarDecl
        { rtvName = resTyName
        , rtvMode = Just modeName
        }
    typeRef = RawTypeRef { rtrMode = Nothing, rtrName = tyName }
    typeArgs = map (RPTVar . rtvName) tyVars
    selfArgs = typeArgs
    selfTyCon = RPTCon typeRef selfArgs
    caseNames = map (\ctorDecl -> "case_" <> rpcName ctorDecl) ctors
    foldCall =
      RDGen
        foldName
        (Just (map RGPos (typeArgs <> [RPTVar resTyName])))
        (Just (map RBAMeta caseNames))

    isRecursiveArg arg =
      arg == selfTyCon
        || (null selfArgs && arg == RPTVar tyName)

    foldGen =
      RawPolyGenDecl
        { rpgName = foldName
        , rpgVars = map RPDType tyVars <> [RPDType resTyVarDecl]
        , rpgDom = RIPort selfTyCon : map foldBinder ctors
        , rpgCod = [RPTVar resTyName]
        , rpgMode = modeName
        }

    foldBinder ctorDecl =
      let convertedArgs =
            map
              (\arg -> if isRecursiveArg arg then RPTVar resTyName else arg)
              (rpcArgs ctorDecl)
          binderVars =
            zipWith
              (\i ty ->
                  RawBinderVarDecl
                    { rbvName = "x" <> T.pack (show i)
                    , rbvType = ty
                    }
              )
              [0 :: Int ..]
              convertedArgs
       in RIBinder binderVars [RPTVar resTyName]

    foldRules = zipWith mkFoldRule ctors caseNames

    mkFoldRule ctorDecl thisCaseName =
      let ctorName = rpcName ctorDecl
          ruleName = foldName <> "_" <> ctorName
          ctorCall = RDGen ctorName (Just (map RGPos typeArgs)) Nothing
          lhs = RDComp ctorCall foldCall
          perArg arg =
            if isRecursiveArg arg
              then foldCall
              else RDId [arg]
          mappedArgs =
            case map perArg (rpcArgs ctorDecl) of
              [] -> RDId []
              ds -> tensorMany ds
          rhs = RDComp mappedArgs (RDSplice thisCaseName)
       in RawPolyRuleDecl
            { rprClass = Computational
            , rprName = ruleName
            , rprOrient = LR
            , rprVars = map RPDType tyVars <> [RPDType resTyVarDecl]
            , rprDom = rpcArgs ctorDecl
            , rprCod = [RPTVar resTyName]
            , rprMode = modeName
            , rprLHS = lhs
            , rprRHS = rhs
            }

    tensorMany [] = RDId []
    tensorMany [d] = d
    tensorMany (d:ds) = RDTensor d (tensorMany ds)

elabActionImage
  :: ModuleEnv
  -> Doctrine
  -> ModName
  -> ModeName
  -> ModeName
  -> (Text, RawDiagExpr)
  -> Either Text (GenName, Diagram)
elabActionImage env doc modName srcMode tgtMode (genNameTxt, rhs) = do
  let g = GenName genNameTxt
  genDecl <-
    lookupGenDeclInDoctrine
      ("Unknown generator in action image: " <> genNameTxt <> " @" <> renderMode srcMode)
      doc
      srcMode
      g
  rejectImplicitTopLevelArgs rhs
  let slots = [ bs | InBinder bs <- gdDom genDecl ]
  let holes = binderHoleNames (length slots)
  let me = ModExpr { meSrc = srcMode, meTgt = tgtMode, mePath = [modName] }
  codeLift <- classifierLiftForModExpr (dModes doc) me
  let mapObj = mapTypeByModExprWithLift doc me codeLift
  let mapTmCtxObj ty =
        if objOwnerMode ty == srcMode
          then mapObj ty
          else Right ty
  let mapBinderSig bs = do
        tmCtx' <- mapM mapTmCtxObj (bsTmCtx bs)
        dom' <- mapM mapObj (bsDom bs)
        cod' <- mapM mapObj (bsCod bs)
        pure bs { bsTmCtx = tmCtx', bsDom = dom', bsCod = cod' }
  mappedSlots <- mapM mapBinderSig slots
  let binderSigs = M.fromList (zip holes mappedSlots)
  let tyVars = gdTyVars genDecl
  let tmVars = gdTmVars genDecl
  (d, _) <- elabDiagExprWith env doc tgtMode [] tyVars tmVars binderSigs BMUse True False rhs
  ensureAcyclicMode doc tgtMode d
  pure (g, d)
  where
    renderMode (ModeName name) = name

    rejectImplicitTopLevelArgs expr =
      case expr of
        RDGen tgtName Nothing _ -> do
          tgtGen <-
            lookupGenDeclInDoctrine
              ("Unknown target generator in action image: " <> tgtName <> " @" <> renderMode tgtMode)
              doc
              tgtMode
              (GenName tgtName)
          if null (gdParams tgtGen)
            then Right ()
            else
              Left
                ( "action image for "
                    <> genNameTxt
                    <> " must provide explicit generator arguments for target "
                    <> tgtName
                )
        _ ->
          Right ()


validateObligationExprMode :: Doctrine -> ModeName -> Bool -> RawOblExpr -> Either Text ()
validateObligationExprMode doc mode allowGen = go mode
  where
    rootMode = mode

    go expected expr =
      case expr of
        ROEDiag _ ->
          Right ()
        ROEMap rawMe inner -> do
          me <- elabRawModExpr (dModes doc) rawMe
          if meTgt me == expected
            then go (meSrc me) inner
            else Left "obligation map: mapped diagram mode does not match surrounding expression mode"
        ROEGen ->
          if allowGen && expected == rootMode
            then Right ()
            else
              if allowGen
                then Left "obligation: @gen is only valid at the obligation mode"
                else Left "obligation: @gen is only valid in for_gen obligations"
        ROELiftDom _ ->
          if allowGen && expected == rootMode
            then Right ()
            else
              if allowGen
                then Left "obligation: lift_dom is only valid at the obligation mode"
                else Left "obligation: lift_dom is only valid in for_gen obligations"
        ROELiftCod _ ->
          if allowGen && expected == rootMode
            then Right ()
            else
              if allowGen
                then Left "obligation: lift_cod is only valid at the obligation mode"
                else Left "obligation: lift_cod is only valid in for_gen obligations"
        ROEComp a b ->
          go expected a >> go expected b
        ROETensor a b ->
          go expected a >> go expected b
