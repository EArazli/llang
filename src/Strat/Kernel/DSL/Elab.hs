{-# LANGUAGE OverloadedStrings #-}
module Strat.Kernel.DSL.Elab
  ( elabRawFile
  , elabRawFileWithEnv
  , elabPresentation
  ) where

import Strat.Kernel.DSL.AST
import Strat.Kernel.DoctrineExpr
import Strat.Kernel.Presentation
import Strat.Kernel.Rule
import Strat.Kernel.Signature
import Strat.Kernel.Term
import Strat.Kernel.Syntax
import Strat.Kernel.RewriteSystem (RewritePolicy(..))
import Strat.Syntax.Spec
import Strat.Model.Spec
import Strat.Frontend.Env
import Strat.Frontend.RunSpec
import Strat.Surface2.Elab
import Strat.Surface2.Def
import Strat.Surface2.SyntaxSpec
import Strat.Surface2.Interface
import qualified Data.Map.Strict as M
import Data.Text (Text)
import qualified Data.Text as T
import Control.Monad (foldM)


data Def = Def
  { defExpr :: DocExpr
  , defRawPresentation :: Maybe Presentation
  }

type DocEnv = M.Map Text Def
type VarEnv = M.Map Text (Var, Sort)

elabRawFile :: RawFile -> Either Text ModuleEnv
elabRawFile = elabRawFileWithEnv emptyEnv

elabRawFileWithEnv :: ModuleEnv -> RawFile -> Either Text ModuleEnv
elabRawFileWithEnv baseEnv (RawFile decls) = do
  let baseDocEnv = docsFromEnv baseEnv
  (docEnv, env) <- foldM step (baseDocEnv, baseEnv) decls
  let env' = env { meDoctrines = M.map defExpr docEnv }
  pure env'
  where
    step (docEnv, env) decl =
      case decl of
        DeclImport _ -> Right (docEnv, env)
        DeclWhere name items -> do
          ensureAbsent "doctrine" name (meDoctrines env)
          pres <- elabPresentation name items
          let def = Def { defExpr = Atom name pres, defRawPresentation = Just pres }
          let docEnv' = M.insert name def docEnv
          pure (docEnv', env
            { meDoctrines = M.insert name (defExpr def) (meDoctrines env)
            , mePresentations = M.insert name pres (mePresentations env)
            })
        DeclExpr name expr -> do
          ensureAbsent "doctrine" name (meDoctrines env)
          dexpr <- resolveExpr docEnv expr
          let def = Def { defExpr = dexpr, defRawPresentation = Nothing }
          let docEnv' = M.insert name def docEnv
          pure (docEnv', env { meDoctrines = M.insert name dexpr (meDoctrines env) })
        DeclSyntaxWhere name items -> do
          ensureAbsent "syntax" name (meSyntaxes env)
          spec <- elabSyntaxSpec name items
          let env' = env { meSyntaxes = M.insert name spec (meSyntaxes env) }
          pure (docEnv, env')
        DeclModelWhere name items -> do
          ensureAbsent "model" name (meModels env)
          spec <- elabModelSpec name items
          let env' = env { meModels = M.insert name spec (meModels env) }
          pure (docEnv, env')
        DeclSurfaceWhere surfDecl -> do
          let name = rsdName surfDecl
          ensureAbsent "surface" name (meSurfaces env)
          def <- elabSurfaceDecl surfDecl
          let env' = env { meSurfaces = M.insert name def (meSurfaces env) }
          pure (docEnv, env')
        DeclSurfaceSyntaxWhere synDecl -> do
          let name = rssName synDecl
          ensureAbsent "surface_syntax" name (meSurfaceSyntaxes env)
          spec <- elabSurfaceSyntaxDecl synDecl
          let env' = env { meSurfaceSyntaxes = M.insert name spec (meSurfaceSyntaxes env) }
          pure (docEnv, env')
        DeclInterfaceWhere ifaceDecl -> do
          let name = ridName ifaceDecl
          ensureAbsent "interface" name (meInterfaces env)
          spec <- elabInterfaceDecl ifaceDecl
          let env' = env { meInterfaces = M.insert name spec (meInterfaces env) }
          pure (docEnv, env')
        DeclRun rawRun -> do
          case meRun env of
            Just _ -> Left "Multiple run blocks found"
            Nothing -> do
              runSpec <- elabRun rawRun
              pure (docEnv, env { meRun = Just runSpec })

    docsFromEnv env =
      M.mapWithKey
        (\name expr -> Def { defExpr = expr, defRawPresentation = M.lookup name (mePresentations env) })
        (meDoctrines env)

ensureAbsent :: Text -> Text -> M.Map Text v -> Either Text ()
ensureAbsent label name mp =
  if M.member name mp
    then Left ("Duplicate " <> label <> " name: " <> name)
    else Right ()

elabPresentation :: Text -> [RawItem] -> Either Text Presentation
elabPresentation name items = do
  (sig, eqs) <- foldM step (Signature M.empty M.empty, []) items
  pure Presentation { presName = name, presSig = sig, presEqs = eqs }
  where
    step (sig, eqs) item =
      case item of
        ItemSort decl -> do
          sig' <- addSortDecl sig decl
          pure (sig', eqs)
        ItemOp decl -> do
          sig' <- addOpDecl sig decl
          pure (sig', eqs)
        ItemRule rr -> do
          eq <- elabRule sig rr
          pure (sig, eqs <> [eq])

addSortDecl :: Signature -> RawSortDecl -> Either Text Signature
addSortDecl sig decl = do
  let name = SortName (rsName decl)
  if M.member name (sigSortCtors sig)
    then Left ("Duplicate sort ctor: " <> rsName decl)
    else do
      params <- mapM (elabSort sig M.empty) (rsParams decl)
      let ctor = SortCtor { scName = name, scParamSort = params }
      pure sig { sigSortCtors = M.insert name ctor (sigSortCtors sig) }

addOpDecl :: Signature -> RawOpDecl -> Either Text Signature
addOpDecl sig decl = do
  let name = OpName (roName decl)
  if M.member name (sigOps sig)
    then Left ("Duplicate op: " <> roName decl)
    else do
      let scope = ScopeId ("op:" <> roName decl)
      (tele, env) <- elabBinders sig scope (roTele decl)
      res <- elabSort sig env (roResult decl)
      let opDecl = OpDecl { opName = name, opTele = tele, opResult = res }
      pure sig { sigOps = M.insert name opDecl (sigOps sig) }

elabRule :: Signature -> RawRule -> Either Text Equation
elabRule sig rr = do
  let scope = ScopeId ("eq:" <> rrName rr)
  (tele, env) <- elabBinders sig scope (rrTele rr)
  lhsTerm <- elabTerm sig env (rrLHS rr)
  rhsTerm <- elabTerm sig env (rrRHS rr)
  pure Equation
    { eqName = rrName rr
    , eqClass = rrClass rr
    , eqOrient = rrOrient rr
    , eqTele = tele
    , eqLHS = lhsTerm
    , eqRHS = rhsTerm
    }

elabBinders :: Signature -> ScopeId -> [RawBinder] -> Either Text ([Binder], VarEnv)
elabBinders sig scope binders =
  foldM step ([], M.empty, 0) binders >>= \(bs, env, _) -> pure (bs, env)
  where
    step (acc, env, ix) (RawBinder name sRaw) = do
      if M.member name env
        then Left ("Duplicate binder name: " <> name)
        else do
          let v = Var scope ix
          s <- elabSort sig env sRaw
          let env' = M.insert name (v, s) env
          pure (acc <> [Binder v s], env', ix + 1)

elabTerm :: Signature -> VarEnv -> RawTerm -> Either Text Term
elabTerm sig env tm =
  case tm of
    RVar v ->
      case M.lookup v env of
        Nothing -> Left ("Unknown variable: " <> v)
        Just (var, s) -> Right (mkVar s var)
    RApp name args -> do
      args' <- mapM (elabTerm sig env) args
      case mkOp sig (OpName name) args' of
        Left err -> Left (renderTypeError err)
        Right t -> Right t

elabSort :: Signature -> VarEnv -> RawSort -> Either Text Sort
elabSort sig env (RawSort name idx) = do
  idxTerms <- mapM (elabTerm sig env) idx
  case mkSort sig (SortName name) idxTerms of
    Left err -> Left (renderSortError err)
    Right s -> Right s

resolveExpr :: DocEnv -> RawExpr -> Either Text DocExpr
resolveExpr env expr =
  case expr of
    ERef name ->
      case M.lookup name env of
        Nothing -> Left ("Unknown doctrine: " <> name)
        Just def -> Right (defExpr def)
    EInst base ns ->
      case M.lookup base env of
        Nothing -> Left ("Unknown doctrine: " <> base)
        Just def ->
          case defRawPresentation def of
            Nothing -> Left ("@ requires a where-defined doctrine: " <> base)
            Just pres -> Right (Atom ns pres)
    EAnd a b -> And <$> resolveExpr env a <*> resolveExpr env b
    ERenameOps m e -> RenameOps (mapOpNames m) <$> resolveExpr env e
    ERenameSorts m e -> RenameSorts (mapSortNames m) <$> resolveExpr env e
    ERenameEqs m e -> RenameEqs m <$> resolveExpr env e
    EShareOps pairs e -> ShareOps (mapPair OpName pairs) <$> resolveExpr env e
    EShareSorts pairs e -> ShareSorts (mapPair SortName pairs) <$> resolveExpr env e

mapOpNames :: M.Map Text Text -> M.Map OpName OpName
mapOpNames m = M.fromList [(OpName k, OpName v) | (k, v) <- M.toList m]

mapSortNames :: M.Map Text Text -> M.Map SortName SortName
mapSortNames m = M.fromList [(SortName k, SortName v) | (k, v) <- M.toList m]

mapPair :: (Text -> a) -> [(Text, Text)] -> [(a, a)]
mapPair f = map (\(a, b) -> (f a, f b))

elabSyntaxSpec :: Text -> [RawSyntaxItem] -> Either Text SyntaxSpec
elabSyntaxSpec name items =
  foldM step initial items
  where
    initial = SyntaxSpec
      { ssName = name
      , ssNotations = []
      , ssAllowCall = False
      , ssVarPrefix = "?"
      , ssAllowQualId = True
      }

    step spec item =
      case item of
        RSAllowCall -> pure spec { ssAllowCall = True }
        RSVarPrefix pfx -> pure spec { ssVarPrefix = pfx }
        RSPrint note -> pure spec { ssNotations = ssNotations spec <> [toNotation True note] }
        RSParse note -> pure spec { ssNotations = ssNotations spec <> [toNotation False note] }

    toNotation printable note =
      case note of
        RNAtom tok op -> NotationSpec NAtom tok op printable
        RNPrefix prec tok op -> NotationSpec (NPrefix prec) tok op printable
        RNPostfix prec tok op -> NotationSpec (NPostfix prec) tok op printable
        RNInfix assoc prec tok op -> NotationSpec (NInfix (toAssoc assoc) prec) tok op printable

    toAssoc a =
      case a of
        AssocL -> LeftAssoc
        AssocR -> RightAssoc
        AssocN -> NonAssoc

elabModelSpec :: Text -> [RawModelItem] -> Either Text ModelSpec
elabModelSpec name items = do
  let defaults = [ d | RMDefault d <- items ]
  def <-
    case defaults of
      [] -> Right DefaultSymbolic
      [RawDefaultSymbolic] -> Right DefaultSymbolic
      [RawDefaultError msg] -> Right (DefaultError msg)
      _ -> Left "Multiple default clauses in model"
  let clauses = [ c | RMOp c <- items ]
  let opNames = map rmcOp clauses
  case findDup opNames of
    Just dup -> Left ("Duplicate op clause in model: " <> dup)
    Nothing -> pure ()
  let ops = map (\c -> OpClause (rmcOp c) (rmcArgs c) (rmcExpr c)) clauses
  pure ModelSpec
    { msName = name
    , msClauses = ops
    , msDefault = def
    }
  where
    findDup xs = go M.empty xs
    go _ [] = Nothing
    go seen (x:rest)
      | M.member x seen = Just x
      | otherwise = go (M.insert x () seen) rest

elabRun :: RawRun -> Either Text RunSpec
elabRun raw = do
  doctrine <- maybe (Left "run: missing doctrine") Right (rrDoctrine raw)
  model <- maybe (Left "run: missing model") Right (rrModel raw)
  policy <- maybe (Right UseOnlyComputationalLR) parsePolicy (rrPolicy raw)
  let fuel = maybe 50 id (rrFuel raw)
  let showFlags = if null (rrShowFlags raw) then [ShowNormalized, ShowValue, ShowCat] else map toShow (rrShowFlags raw)
  validateRunFields (rrSurface raw) (rrSurfaceSyntax raw) (rrInterface raw) (rrSyntax raw)
  pure RunSpec
    { runDoctrine = doctrine
    , runSyntax = rrSyntax raw
    , runCoreSyntax = rrCoreSyntax raw
    , runSurface = rrSurface raw
    , runSurfaceSyntax = rrSurfaceSyntax raw
    , runInterface = rrInterface raw
    , runModel = model
    , runOpen = rrOpen raw
    , runPolicy = policy
    , runFuel = fuel
    , runShowFlags = showFlags
    , runExprText = rrExprText raw
    }
  where
    parsePolicy name =
      case name of
        "UseOnlyComputationalLR" -> Right UseOnlyComputationalLR
        "UseStructuralAsBidirectional" -> Right UseStructuralAsBidirectional
        "UseAllOriented" -> Right UseAllOriented
        _ -> Left ("Unknown policy: " <> name)

    toShow s =
      case s of
        RawShowNormalized -> ShowNormalized
        RawShowValue -> ShowValue
        RawShowCat -> ShowCat
        RawShowInput -> ShowInput

validateRunFields :: Maybe Text -> Maybe Text -> Maybe Text -> Maybe Text -> Either Text ()
validateRunFields surf surfSyn iface coreSyn =
  case surf of
    Nothing ->
      case coreSyn of
        Nothing -> Left "run: missing syntax"
        Just _ -> Right ()
    Just _ -> do
      if surfSyn == Nothing then Left "run: missing surface_syntax" else Right ()
      if iface == Nothing then Left "run: missing interface" else Right ()

renderTypeError :: TypeError -> Text
renderTypeError = T.pack . show

renderSortError :: SortError -> Text
renderSortError = T.pack . show
