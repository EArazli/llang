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
    P.RPMode decl ->
      P.RPMode
        decl
          { P.rmdName = lookupText subst (P.rmdName decl)
          }
    P.RPIndexMode name -> P.RPIndexMode (lookupText subst name)
    P.RPIndexFun decl ->
      P.RPIndexFun
        decl
          { P.rifName = lookupText subst (P.rifName decl)
          , P.rifArgs = map (substIxVarDecl subst) (P.rifArgs decl)
          , P.rifRes = substTypeExpr subst (P.rifRes decl)
          , P.rifMode = lookupText subst (P.rifMode decl)
          }
    P.RPIndexRule decl ->
      P.RPIndexRule
        decl
          { P.rirName = lookupText subst (P.rirName decl)
          , P.rirVars = map (substIxVarDecl subst) (P.rirVars decl)
          , P.rirLHS = substTypeExpr subst (P.rirLHS decl)
          , P.rirRHS = substTypeExpr subst (P.rirRHS decl)
          , P.rirMode = lookupText subst (P.rirMode decl)
          }
    P.RPStructure decl ->
      P.RPStructure decl { P.rsMode = lookupText subst (P.rsMode decl) }
    P.RPModality decl ->
      P.RPModality
        decl
          { P.rmodName = lookupText subst (P.rmodName decl)
          , P.rmodSrc = lookupText subst (P.rmodSrc decl)
          , P.rmodTgt = lookupText subst (P.rmodTgt decl)
          }
    P.RPModEq decl ->
      P.RPModEq
        decl
          { P.rmeLHS = substModExpr subst (P.rmeLHS decl)
          , P.rmeRHS = substModExpr subst (P.rmeRHS decl)
          }
    P.RPAdjunction decl ->
      P.RPAdjunction
        decl
          { P.raLeft = lookupText subst (P.raLeft decl)
          , P.raRight = lookupText subst (P.raRight decl)
          }
    P.RPAttrSort decl ->
      P.RPAttrSort decl
        { P.rasName = lookupText subst (P.rasName decl)
        , P.rasKind = fmap (lookupText subst) (P.rasKind decl)
        }
    P.RPType decl ->
      P.RPType decl
        { P.rptName = lookupText subst (P.rptName decl)
        , P.rptVars = map (substParamDecl subst) (P.rptVars decl)
        , P.rptMode = lookupText subst (P.rptMode decl)
        }
    P.RPGen decl ->
      P.RPGen decl
        { P.rpgName = lookupText subst (P.rpgName decl)
        , P.rpgVars = map (substParamDecl subst) (P.rpgVars decl)
        , P.rpgAttrs = [ (lookupText subst field, lookupText subst sortName) | (field, sortName) <- P.rpgAttrs decl ]
        , P.rpgDom = map (substInputShape subst) (P.rpgDom decl)
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
        , P.rprVars = map (substParamDecl subst) (P.rprVars decl)
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

substIxVarDecl :: M.Map Text Text -> P.RawIxVarDecl -> P.RawIxVarDecl
substIxVarDecl subst decl =
  decl
    { P.rivSort = substTypeExpr subst (P.rivSort decl)
    }

substParamDecl :: M.Map Text Text -> P.RawParamDecl -> P.RawParamDecl
substParamDecl subst decl =
  case decl of
    P.RPDType tv -> P.RPDType (substTyVarDecl subst tv)
    P.RPDIndex iv -> P.RPDIndex (substIxVarDecl subst iv)

substTypeExpr :: M.Map Text Text -> P.RawPolyTypeExpr -> P.RawPolyTypeExpr
substTypeExpr subst expr =
  case expr of
    P.RPTVar name -> P.RPTVar (lookupText subst name)
    P.RPTBound i -> P.RPTBound i
    P.RPTCon ref args ->
      P.RPTCon (substTypeRef subst ref) (map (substTypeExpr subst) args)
    P.RPTMod me inner ->
      P.RPTMod (substModExpr subst me) (substTypeExpr subst inner)

substInputShape :: M.Map Text Text -> P.RawInputShape -> P.RawInputShape
substInputShape subst shape =
  case shape of
    P.RIPort ty -> P.RIPort (substTypeExpr subst ty)
    P.RIBinder vars cod ->
      P.RIBinder
        (map substBinderVar vars)
        (map (substTypeExpr subst) cod)
  where
    substBinderVar v =
      v
        { P.rbvType = substTypeExpr subst (P.rbvType v)
        }

substModExpr :: M.Map Text Text -> P.RawModExpr -> P.RawModExpr
substModExpr subst me =
  case me of
    P.RMId modeName -> P.RMId (lookupText subst modeName)
    P.RMComp toks -> P.RMComp (map (lookupText subst) toks)

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
    P.RDMetaVar name -> P.RDMetaVar (lookupText subst name)
    P.RDGen name mArgs mAttrArgs mBArgs ->
      P.RDGen
        (lookupText subst name)
        (fmap (map (substTypeExpr subst)) mArgs)
        (fmap (map (substAttrArg subst)) mAttrArgs)
        (fmap (map (substBinderArg subst)) mBArgs)
    P.RDTermRef name -> P.RDTermRef (lookupText subst name)
    P.RDSplice name -> P.RDSplice (lookupText subst name)
    P.RDBox name inner -> P.RDBox (lookupText subst name) (substDiagExpr subst inner)
    P.RDLoop inner -> P.RDLoop (substDiagExpr subst inner)
    P.RDComp a b -> P.RDComp (substDiagExpr subst a) (substDiagExpr subst b)
    P.RDTensor a b -> P.RDTensor (substDiagExpr subst a) (substDiagExpr subst b)

substBinderArg :: M.Map Text Text -> P.RawBinderArg -> P.RawBinderArg
substBinderArg subst barg =
  case barg of
    P.RBAExpr e -> P.RBAExpr (substDiagExpr subst e)
    P.RBAMeta name -> P.RBAMeta (lookupText subst name)

substAttrArg :: M.Map Text Text -> P.RawAttrArg -> P.RawAttrArg
substAttrArg subst arg =
  case arg of
    P.RAName name term -> P.RAName (lookupText subst name) (substAttrTerm subst term)
    P.RAPos term -> P.RAPos (substAttrTerm subst term)

substAttrTerm :: M.Map Text Text -> P.RawAttrTerm -> P.RawAttrTerm
substAttrTerm subst term =
  case term of
    P.RATVar name -> P.RATVar (lookupText subst name)
    P.RATInt n -> P.RATInt n
    P.RATString s -> P.RATString s
    P.RATBool b -> P.RATBool b

lookupText :: M.Map Text Text -> Text -> Text
lookupText subst name = M.findWithDefault name name subst
