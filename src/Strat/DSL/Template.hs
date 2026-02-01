{-# LANGUAGE OverloadedStrings #-}
module Strat.DSL.Template
  ( instantiateTemplate
  , substRawPolyDoctrine
  ) where

import Data.Text (Text)
import qualified Data.Map.Strict as M
import Strat.DSL.AST (RawDoctrineTemplate(..))
import qualified Strat.Poly.DSL.AST as P


instantiateTemplate :: RawDoctrineTemplate -> Text -> [Text] -> Either Text P.RawPolyDoctrine
instantiateTemplate tmpl newName args =
  if length args /= length (rdtParams tmpl)
    then Left "doctrine_template: argument arity mismatch"
    else
      let subst = M.fromList (zip (rdtParams tmpl) args)
          body = substRawPolyDoctrine subst (rdtBody tmpl)
      in Right body { P.rpdName = newName }

substRawPolyDoctrine :: M.Map Text Text -> P.RawPolyDoctrine -> P.RawPolyDoctrine
substRawPolyDoctrine subst doc =
  doc
    { P.rpdName = subText (P.rpdName doc)
    , P.rpdExtends = fmap subText (P.rpdExtends doc)
    , P.rpdItems = map (substItem subst) (P.rpdItems doc)
    }
  where
    subText = lookupText subst

substItem :: M.Map Text Text -> P.RawPolyItem -> P.RawPolyItem
substItem subst item =
  case item of
    P.RPMode name -> P.RPMode (lookupText subst name)
    P.RPType decl ->
      P.RPType decl
        { P.rptName = lookupText subst (P.rptName decl)
        , P.rptVars = map (substTyVarDecl subst) (P.rptVars decl)
        , P.rptMode = lookupText subst (P.rptMode decl)
        }
    P.RPGen decl ->
      P.RPGen decl
        { P.rpgName = lookupText subst (P.rpgName decl)
        , P.rpgVars = map (substTyVarDecl subst) (P.rpgVars decl)
        , P.rpgDom = map (substTypeExpr subst) (P.rpgDom decl)
        , P.rpgCod = map (substTypeExpr subst) (P.rpgCod decl)
        , P.rpgMode = lookupText subst (P.rpgMode decl)
        }
    P.RPRule decl ->
      P.RPRule decl
        { P.rprMode = lookupText subst (P.rprMode decl)
        , P.rprDom = map (substTypeExpr subst) (P.rprDom decl)
        , P.rprCod = map (substTypeExpr subst) (P.rprCod decl)
        , P.rprLHS = substDiagExpr subst (P.rprLHS decl)
        , P.rprRHS = substDiagExpr subst (P.rprRHS decl)
        , P.rprVars = map (substTyVarDecl subst) (P.rprVars decl)
        }
    P.RPData decl ->
      P.RPData decl
        { P.rpdTyName = lookupText subst (P.rpdTyName decl)
        , P.rpdTyVars = map (substTyVarDecl subst) (P.rpdTyVars decl)
        , P.rpdTyMode = lookupText subst (P.rpdTyMode decl)
        , P.rpdCtors = map (substCtor subst) (P.rpdCtors decl)
        }

substCtor :: M.Map Text Text -> P.RawPolyCtorDecl -> P.RawPolyCtorDecl
substCtor subst decl =
  decl
    { P.rpcName = lookupText subst (P.rpcName decl)
    , P.rpcArgs = map (substTypeExpr subst) (P.rpcArgs decl)
    }

substTyVarDecl :: M.Map Text Text -> P.RawTyVarDecl -> P.RawTyVarDecl
substTyVarDecl subst decl =
  decl { P.rtvMode = fmap (lookupText subst) (P.rtvMode decl) }

substTypeExpr :: M.Map Text Text -> P.RawPolyTypeExpr -> P.RawPolyTypeExpr
substTypeExpr subst expr =
  case expr of
    P.RPTVar name -> P.RPTVar name
    P.RPTCon ref args ->
      P.RPTCon (substTypeRef subst ref) (map (substTypeExpr subst) args)

substTypeRef :: M.Map Text Text -> P.RawTypeRef -> P.RawTypeRef
substTypeRef subst ref =
  ref
    { P.rtrMode = fmap (lookupText subst) (P.rtrMode ref)
    , P.rtrName = lookupText subst (P.rtrName ref)
    }

substDiagExpr :: M.Map Text Text -> P.RawDiagExpr -> P.RawDiagExpr
substDiagExpr subst expr =
  case expr of
    P.RDId ctx -> P.RDId (map (substTypeExpr subst) ctx)
    P.RDGen name mArgs ->
      P.RDGen (lookupText subst name) (fmap (map (substTypeExpr subst)) mArgs)
    P.RDTermRef name -> P.RDTermRef (lookupText subst name)
    P.RDBox name inner -> P.RDBox (lookupText subst name) (substDiagExpr subst inner)
    P.RDLoop inner -> P.RDLoop (substDiagExpr subst inner)
    P.RDComp a b -> P.RDComp (substDiagExpr subst a) (substDiagExpr subst b)
    P.RDTensor a b -> P.RDTensor (substDiagExpr subst a) (substDiagExpr subst b)

lookupText :: M.Map Text Text -> Text -> Text
lookupText subst name = M.findWithDefault name name subst
