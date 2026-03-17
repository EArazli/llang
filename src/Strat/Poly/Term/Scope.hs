{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Term.Scope
  ( hostBoundGlobalsExpr
  , hostMaxTmScopeExpr
  , renameTermGlobalsPartial
  , instantiateMetaBodyWith
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.Obj
  ( Obj
  , TmVar(..)
  , defaultMetaArgs
  )
import Strat.Poly.Term.AST
  ( TermExpr(..)
  , TermHeadArg(..)
  , boundGlobalsObj
  , maxTmScopeObj
  )

hostBoundGlobalsExpr :: TermExpr -> S.Set Int
hostBoundGlobalsExpr tm =
  case tm of
    TMBound i -> S.singleton i
    TMMeta _ args -> S.fromList args
    TMHead _ args _ -> S.unions (map boundHeadArg args)
    TMSplice _ _ args -> S.unions (map hostBoundGlobalsExpr args)
    TMLit _ -> S.empty
  where
    boundHeadArg arg =
      case arg of
        THAObj obj -> boundGlobalsObj obj
        THATm inner -> hostBoundGlobalsExpr inner

hostMaxTmScopeExpr :: TermExpr -> Int
hostMaxTmScopeExpr tm =
  case tm of
    TMBound _ -> 0
    TMMeta v _ -> tmvScope v
    TMHead _ args _ -> maximum (0 : map maxHeadArg args)
    TMSplice _ _ args -> maximum (0 : map hostMaxTmScopeExpr args)
    TMLit _ -> 0
  where
    maxHeadArg arg =
      case arg of
        THAObj obj -> maxTmScopeObj obj
        THATm inner -> hostMaxTmScopeExpr inner

renameTermGlobalsPartial :: M.Map Int Int -> TermExpr -> Either Text TermExpr
renameTermGlobalsPartial ren tm =
  case tm of
    TMBound i -> Right (TMBound (M.findWithDefault i i ren))
    TMMeta v args -> Right (TMMeta v (map (\i -> M.findWithDefault i i ren) args))
    -- Binder payload diagrams carry their own local term-context, so host
    -- global-index renaming does not penetrate them.
    TMHead f args bargs -> do
      args' <- mapM renameHeadArg args
      Right (TMHead f args' bargs)
    TMSplice hole me args ->
      TMSplice hole me <$> mapM (renameTermGlobalsPartial ren) args
    TMLit lit -> Right (TMLit lit)
  where
    renameHeadArg arg =
      case arg of
        THAObj obj -> Right (THAObj obj)
        THATm tm0 -> THATm <$> renameTermGlobalsPartial ren tm0

instantiateMetaBodyWith
  :: Text
  -> [Obj]
  -> TmVar
  -> [Int]
  -> TermExpr
  -> Either Text TermExpr
instantiateMetaBodyWith site tmCtx v spine body = do
  let formal = defaultMetaArgs tmCtx v
      scope = tmvScope v
  if length formal == scope
    then Right ()
    else Left (site <> ": default-meta spine arity does not match scope")
  if length spine == scope
    then Right ()
    else
      Left
        ( site
            <> ": occurrence spine arity mismatch for "
            <> tmvName v
            <> " (expected "
            <> T.pack (show scope)
            <> ", got "
            <> T.pack (show (length spine))
            <> ")"
        )
  let ren = M.fromList (zip formal spine)
  renameTermGlobalsPartial ren body
