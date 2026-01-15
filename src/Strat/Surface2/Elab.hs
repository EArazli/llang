{-# LANGUAGE OverloadedStrings #-}
module Strat.Surface2.Elab
  ( elabSurfaceDecl
  , elabSurfaceSyntaxDecl
  , elabInterfaceDecl
  ) where

import Strat.Kernel.DSL.AST
import Strat.Surface2.Term
import Strat.Surface2.Pattern
import Strat.Surface2.Def
import Strat.Surface2.SyntaxSpec
import Strat.Surface2.Interface
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import Control.Monad (foldM)

elabSurfaceDecl :: RawSurfaceDecl -> Either Text SurfaceDef
elabSurfaceDecl (RawSurfaceDecl name items) = do
  let sortNames = [ Sort2Name s | RSSort s <- items ]
  let sorts = M.fromList [(s, ()) | s <- sortNames]
  ctxSortName <- case [ s | RSContextSort s <- items ] of
    [] -> Left "surface missing context_sort"
    (s:_) -> Right (Sort2Name s)
  if M.member ctxSortName sorts
    then Right ()
    else Left ("context_sort not declared: " <> renderSort2 ctxSortName)
  reqIface <- case [ n | RSRequiresInterface n <- items ] of
    [] -> Left "surface missing requires interface"
    (n:_) -> Right n
  cons <- buildConstructors sorts items
  validateBinderTypes ctxSortName cons
  judgs <- buildJudgments items
  defs <- buildDefines cons items
  rules <- buildRules cons judgs ctxSortName items
  pure SurfaceDef
    { sdName = name
    , sdSorts = sorts
    , sdContextSort = ctxSortName
    , sdCons = cons
    , sdJudgments = judgs
    , sdRules = rules
    , sdDefines = defs
    , sdRequires = reqIface
    }

validateBinderTypes :: Sort2Name -> M.Map Con2Name ConDecl -> Either Text ()
validateBinderTypes ctxSort cons = do
  mapM_ checkCon (M.elems cons)
  where
    checkCon con = do
      let env = M.fromList [ (caName arg, caSort arg) | arg <- conArgs con ]
      mapM_ (checkArg env) (conArgs con)

    checkArg env arg =
      mapM_ (checkTerm env) (caBinders arg)

    checkTerm env tm = do
      s <- inferSort env tm
      if s == ctxSort
        then Right ()
        else Left ("Binder type does not have context sort: " <> renderSort2 s)

    inferSort env tm =
      case tm of
        SFree name ->
          case M.lookup name env of
            Nothing -> Left ("Unknown surface variable in binder type: " <> name)
            Just s -> Right s
        SBound _ -> Left "Binder types may not reference bound indices"
        SCon con args ->
          case M.lookup con cons of
            Nothing -> Left ("Unknown constructor in binder type: " <> renderCon con)
            Just decl -> do
              let expected = map caSort (conArgs decl)
              if length expected /= length args
                then Left ("Constructor arity mismatch in binder type: " <> renderCon con)
                else do
                  mapM_ (uncurry (checkArgSort env)) (zip expected args)
                  Right (conResult decl)

    checkArgSort env expected (SArg binders body) = do
      mapM_ (checkTerm env) binders
      s <- inferSort env body
      if s == expected
        then Right ()
        else Left ("Constructor argument sort mismatch: expected " <> renderSort2 expected <> ", got " <> renderSort2 s)

renderCon :: Con2Name -> Text
renderCon (Con2Name t) = t

elabSurfaceSyntaxDecl :: RawSurfaceSyntaxDecl -> Either Text SurfaceSyntaxSpec
elabSurfaceSyntaxDecl (RawSurfaceSyntaxDecl name surf items) = do
  let tyNotes = [ toNotation n | RSSTy n <- items ]
  let tmNotes = [ toNotation n | RSSTm n <- items ]
  pure SurfaceSyntaxSpec
    { sssName = name
    , sssSurface = surf
    , sssTyNotations = tyNotes
    , sssTmNotations = tmNotes
    }
  where
    toNotation n =
      case n of
        RSNAtom tok con -> SAtom tok con
        RSNPrefix tok con -> SPrefix tok con
        RSNInfix assoc prec tok con -> SInfix (toAssoc assoc) prec tok con
        RSNBinder tok tySep bodySep con -> SBinder tok tySep bodySep con
        RSNApp con -> SApp con
        RSNTuple tok con -> STuple tok con

    toAssoc a =
      case a of
        SurfAssocL -> SLeft
        SurfAssocR -> SRight
        SurfAssocN -> SNon

elabInterfaceDecl :: RawInterfaceDecl -> Either Text InterfaceSpec
elabInterfaceDecl (RawInterfaceDecl name doc items) = do
  let slots = M.fromList [(riiSlot it, riiTarget it) | it <- items]
  pure InterfaceSpec
    { isName = name
    , isDoctrine = doc
    , isSlots = slots
    }

buildConstructors :: M.Map Sort2Name () -> [RawSurfaceItem] -> Either Text (M.Map Con2Name ConDecl)
buildConstructors sorts items = do
  let conList = [ c | RSCon c <- items ]
  let conNames = [ Con2Name (rscName c) | c <- conList ]
  foldM (step conNames) M.empty conList
  where
    step conNames acc decl = do
      let cname = Con2Name (rscName decl)
      if M.member cname acc
        then Left ("Duplicate constructor: " <> rscName decl)
        else do
          res <- requireSort sorts (rscResult decl)
          args <- mapM (elabConArg conNames sorts) (rscArgs decl)
          pure (M.insert cname (ConDecl cname args res) acc)

elabConArg :: [Con2Name] -> M.Map Sort2Name () -> RawSurfaceArg -> Either Text ConArg
elabConArg conNames sorts arg = do
  res <- requireSort sorts (rsaSort arg)
  binders <- mapM (elabSurfaceTermSimple conNames . snd) (rsaBinders arg)
  pure ConArg
    { caName = rsaName arg
    , caBinders = binders
    , caSort = res
    }

buildJudgments :: [RawSurfaceItem] -> Either Text (M.Map JudgName JudgDecl)
buildJudgments items = foldM step M.empty [ j | RSJudg j <- items ]
  where
    step acc decl = do
      let jname = JudgName (rsjName decl)
      if M.member jname acc
        then Left ("Duplicate judgment: " <> rsjName decl)
        else do
          params <- mapM elabJudgParam (rsjParams decl)
          outs <- mapM elabJudgParam (rsjOutputs decl)
          pure (M.insert jname (JudgDecl jname params outs) acc)

elabJudgParam :: RawSurfaceJudgParam -> Either Text JudgParam
elabJudgParam (RawSurfaceJudgParam name sortName) =
  JudgParam name <$> parseParamSort sortName

parseParamSort :: Text -> Either Text ParamSort
parseParamSort name =
  case name of
    "Ctx" -> Right PCtx
    "Core" -> Right PCore
    "Nat" -> Right PNat
    _ -> Right (PSurf (Sort2Name name))

buildRules :: M.Map Con2Name ConDecl -> M.Map JudgName JudgDecl -> Sort2Name -> [RawSurfaceItem] -> Either Text [RuleDef]
buildRules cons judgs ctxSort items = mapM (elabRule cons judgs ctxSort) [ r | RSRule r <- items ]

elabRule :: M.Map Con2Name ConDecl -> M.Map JudgName JudgDecl -> Sort2Name -> RawSurfaceRule -> Either Text RuleDef
elabRule cons judgs ctxSort rr = do
  premises <- mapM (elabPremise cons judgs ctxSort) (rsrPremises rr)
  concl <- elabConclusion cons judgs ctxSort (rsrConclusion rr)
  pure (RuleDef (rsrName rr) premises concl)

elabPremise :: M.Map Con2Name ConDecl -> M.Map JudgName JudgDecl -> Sort2Name -> RawSurfacePremise -> Either Text RulePremise
elabPremise cons judgs ctxSort prem =
  case prem of
    RPremiseLookup ctx idx out ->
      PremiseLookup <$> pure ctx <*> pure (elabNatPat idx) <*> pure out
    RPremiseJudg name args outs under -> do
      jdecl <- lookupJudg name judgs
      let depthFor param =
            case under of
              Nothing -> 0
              Just _ ->
                case jpSort param of
                  PSurf s | s /= ctxSort -> 1
                  _ -> 0
      argPats <- elabArgPats cons ctxSort depthFor (jdParams jdecl) args
      under' <- mapM (elabUnder cons) under
      pure (PremiseJudg (jdName jdecl) argPats outs under')

elabConclusion :: M.Map Con2Name ConDecl -> M.Map JudgName JudgDecl -> Sort2Name -> RawSurfaceConclusion -> Either Text RuleConclusion
elabConclusion cons judgs ctxSort concl = do
  jdecl <- lookupJudg (rcoName concl) judgs
  argPats <- elabArgPats cons ctxSort (const 0) (jdParams jdecl) (rcoArgs concl)
  let outs = map elabCoreExpr (rcoOutputs concl)
  pure (RuleConclusion (jdName jdecl) argPats outs)

elabArgPats :: M.Map Con2Name ConDecl -> Sort2Name -> (JudgParam -> Int) -> [JudgParam] -> [RawSurfacePat] -> Either Text [ArgPat]
elabArgPats cons ctxSort depthFor params args =
  if length params /= length args
    then Left "Judgment arity mismatch in rule"
    else mapM (\(param, arg) -> elabArgPat cons ctxSort (depthFor param) param arg) (zip params args)

elabArgPat :: M.Map Con2Name ConDecl -> Sort2Name -> Int -> JudgParam -> RawSurfacePat -> Either Text ArgPat
elabArgPat cons ctxSort depth param pat =
  case jpSort param of
    PCtx ->
      case pat of
        RSPVar name -> Right (ArgCtx name)
        _ -> Left "Expected context variable in rule"
    PNat -> Right (ArgNat (elabNatPatFromSurface pat))
    PCore -> Left "Core terms not allowed in judgment inputs"
    PSurf _ -> ArgSurf <$> elabPat cons depth pat
  where
    elabNatPatFromSurface p =
      case p of
        RSPVar name -> NatVar name
        RSPBound n -> NatVar (T.pack (show n))
        RSPBoundVar name -> NatVar name
        _ -> NatVar "i"

elabUnder :: M.Map Con2Name ConDecl -> (Text, Text, RawSurfaceTerm) -> Either Text UnderCtx
elabUnder cons (ctx, name, ty) = do
  pat <- elabPat cons 0 (termToPat ty)
  pure (UnderCtx ctx name pat)

buildDefines :: M.Map Con2Name ConDecl -> [RawSurfaceItem] -> Either Text (M.Map Text Define)
buildDefines cons items = foldM step M.empty [ d | RSDefine d <- items ]
  where
    step acc def = do
      let RawDefine name clauseList = def
      clauses <- mapM (elabDefineClause cons) clauseList
      let newDef =
            case M.lookup name acc of
              Nothing -> Define name clauses
              Just existing -> existing { defClauses = defClauses existing <> clauses }
      pure (M.insert name newDef acc)

elabDefineClause :: M.Map Con2Name ConDecl -> RawDefineClause -> Either Text DefineClause
elabDefineClause cons clause = do
  args <- mapM (elabDefinePat cons) (rdcArgs clause)
  wh <- mapM (elabWhere cons) (rdcWhere clause)
  pure DefineClause
    { dcArgs = args
    , dcBody = elabCoreExpr (rdcBody clause)
    , dcWhere = wh
    }

elabDefinePat :: M.Map Con2Name ConDecl -> RawDefinePat -> Either Text DefinePat
elabDefinePat cons pat =
  case pat of
    RDPVar name ->
      if M.member (Con2Name name) cons
        then Right (DPSurf (PCon (Con2Name name) []))
        else Right (DPVar name)
    RDPNat np -> Right (DPNat (elabNatPat np))
    RDPSurf sp -> DPSurf <$> elabPat cons 0 sp
    RDPCtx cp -> DPCtx <$> elabCtxPat cons cp

elabWhere :: M.Map Con2Name ConDecl -> RawWhereClause -> Either Text WhereClause
elabWhere cons (RawWhereClause name pat) =
  WhereClause name <$> elabCtxPat cons pat

elabCtxPat :: M.Map Con2Name ConDecl -> RawCtxPat -> Either Text CtxPat
elabCtxPat cons pat =
  case pat of
    RCPEmpty -> Right CtxEmpty
    RCPVar v -> Right (CtxVar v)
    RCPExt ctx name ty -> do
      p <- elabPat cons 0 (termToPat ty)
      pure (CtxExtend ctx name p)

elabNatPat :: RawNatPat -> NatPat
elabNatPat np =
  case np of
    RNPZero -> NatZero
    RNPSucc name -> NatSucc name
    RNPVar name -> NatVar name

elabCoreExpr :: RawCoreExpr -> CoreExpr
elabCoreExpr expr =
  case expr of
    RCEVar v -> CoreVar v
    RCEApp f args -> CoreApp f (map elabCoreExpr args)

elabPat :: M.Map Con2Name ConDecl -> Int -> RawSurfacePat -> Either Text PTerm
elabPat cons depth pat =
  case pat of
    RSPBound n -> Right (PBound (Ix n))
    RSPBoundVar name -> Right (PBoundVar name)
    RSPVar name ->
      if M.member (Con2Name name) cons
        then Right (PCon (Con2Name name) [])
        else Right (PMeta (MVar name) (map Ix [0..depth-1]))
    RSPCon name args ->
      case M.lookup (Con2Name name) cons of
        Nothing -> Left ("Unknown constructor: " <> name)
        Just decl -> do
          let conArgsDecl = conArgs decl
          if length args /= length conArgsDecl
            then Left ("Constructor arity mismatch: " <> name)
            else do
              pArgs <- elabConArgs cons depth conArgsDecl args M.empty
              Right (PCon (Con2Name name) pArgs)

elabConArgs :: M.Map Con2Name ConDecl -> Int -> [ConArg] -> [RawSurfacePat] -> M.Map Text PTerm -> Either Text [PArg]
elabConArgs _ _ [] [] _ = Right []
elabConArgs cons depth (argDecl:restDecls) (argPat:restPats) env = do
  let binderTemplates = caBinders argDecl
  binderPats <- mapM (bindersToPattern env) binderTemplates
  let depth' = depth + length binderTemplates
  bodyPat <- elabPat cons depth' argPat
  let env' = M.insert (caName argDecl) bodyPat env
  rest <- elabConArgs cons depth restDecls restPats env'
  pure (PArg binderPats bodyPat : rest)
elabConArgs _ _ _ _ _ = Left "Constructor arity mismatch"

bindersToPattern :: M.Map Text PTerm -> STerm -> Either Text PTerm
bindersToPattern env tm =
  case tm of
    SBound ix -> Right (PBound ix)
    SFree name ->
      case M.lookup name env of
        Just p -> Right p
        Nothing -> Right (PFree name)
    SCon con args ->
      PCon con <$> mapM (bindersArg env) args

bindersArg :: M.Map Text PTerm -> SArg -> Either Text PArg
bindersArg env (SArg binders body) = do
  binders' <- mapM (bindersToPattern env) binders
  body' <- bindersToPattern env body
  pure (PArg binders' body')

elabSurfaceTermSimple :: [Con2Name] -> RawSurfaceTerm -> Either Text STerm
elabSurfaceTermSimple cons tm =
  case tm of
    RSTBound n -> Right (SBound (Ix n))
    RSTVar name ->
      if Con2Name name `elem` cons
        then Right (SCon (Con2Name name) [])
        else Right (SFree name)
    RSTCon name args ->
      if Con2Name name `elem` cons
        then do
          args' <- mapM (elabSurfaceTermSimple cons) args
          Right (SCon (Con2Name name) (map (SArg []) args'))
        else Left ("Unknown constructor: " <> name)

termToPat :: RawSurfaceTerm -> RawSurfacePat
termToPat tm =
  case tm of
    RSTVar name -> RSPVar name
    RSTBound n -> RSPBound n
    RSTCon name args -> RSPCon name (map termToPat args)

lookupJudg :: Text -> M.Map JudgName JudgDecl -> Either Text JudgDecl
lookupJudg name judgs =
  case M.lookup (JudgName name) judgs of
    Nothing -> Left ("Unknown judgment: " <> name)
    Just j -> Right j

requireSort :: M.Map Sort2Name () -> Text -> Either Text Sort2Name
requireSort sorts name =
  let s = Sort2Name name
  in if M.member s sorts
      then Right s
      else Left ("Unknown sort: " <> name)

renderSort2 :: Sort2Name -> Text
renderSort2 (Sort2Name t) = t
