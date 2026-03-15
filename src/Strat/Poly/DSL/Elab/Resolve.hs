{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.DSL.Elab.Resolve
  ( elabRawModExpr
  , unresolvedClassUniverse
  ) where

import Control.Monad (foldM)
import qualified Data.Map.Strict as M
import Data.Text (Text)
import Strat.Poly.DSL.AST
  ( RawModExpr(..)
  , RawPolyObjExpr(..)
  , RawTypeRef(..)
  )
import Strat.Poly.Doctrine (Doctrine(..))
import Strat.Poly.ModeTheory
  ( ModExpr(..)
  , ModName(..)
  , ModeName(..)
  , ModeTheory(..)
  , mdSrc
  , mdTgt
  )
import Strat.Poly.Obj
  ( Obj
  , ObjName(..)
  , ObjRef(..)
  )
import Strat.Poly.ObjClassifier (modeClassifierMode)
import Strat.Poly.PendingUniverse (mkPendingUniverseSeed)

elabRawModExpr :: ModeTheory -> RawModExpr -> Either Text ModExpr
elabRawModExpr mt raw =
  case raw of
    RMId modeName -> do
      let mode = ModeName modeName
      if M.member mode (mtModes mt)
        then Right ModExpr { meSrc = mode, meTgt = mode, mePath = [] }
        else Left ("unknown mode in modality expression: " <> modeName)
    RMComp toks -> do
      path <- mapM requireModName (reverse toks)
      case path of
        [] -> Left "empty modality expression"
        (m0:rest) -> do
          d0 <- requireDecl m0
          tgt <- foldM step (mdTgt d0) rest
          Right
            ModExpr
              { meSrc = mdSrc d0
              , meTgt = tgt
              , mePath = m0 : rest
              }
  where
    requireModName tok =
      let name = ModName tok
       in if M.member name (mtDecls mt)
            then Right name
            else Left ("unknown modality in expression: " <> tok)
    requireDecl name =
      case M.lookup name (mtDecls mt) of
        Nothing -> Left "unknown modality"
        Just decl -> Right decl
    step cur name = do
      decl <- requireDecl name
      if mdSrc decl == cur
        then Right (mdTgt decl)
        else Left "modality composition type mismatch"

unresolvedClassUniverse :: Doctrine -> ModeName -> RawPolyObjExpr -> Either Text Obj
unresolvedClassUniverse doc expectedOwnerMode raw =
  mkPendingUniverseSeed expectedOwnerMode <$> go expectedOwnerMode raw
  where
    mt = dModes doc

    go ownerMode raw =
      case raw of
        RPTVar name ->
          Right
            ObjRef
              { orMode = modeClassifierMode mt ownerMode
              , orName = ObjName name
              }
        RPTMod rawMe innerRaw ->
          case elabRawModExpr mt rawMe of
            Right me ->
              if meTgt me == ownerMode
                then go (meSrc me) innerRaw
                else Left "classifiedBy universe mode mismatch"
            Left _ ->
              go ownerMode innerRaw
        RPTCon rawRef args ->
          case asModalityCall rawRef args of
            Just (rawMe, innerRaw) ->
              case elabRawModExpr mt rawMe of
                Right me ->
                  if meTgt me == ownerMode
                    then go (meSrc me) innerRaw
                    else Left "classifiedBy universe mode mismatch"
                Left _ ->
                  go ownerMode innerRaw
            Nothing ->
              case args of
                [] ->
                  let refMode = maybe (modeClassifierMode mt ownerMode) ModeName (rtrMode rawRef)
                   in Right
                        ObjRef
                          { orMode = refMode
                          , orName = ObjName (rtrName rawRef)
                          }
                [innerRaw] ->
                  go ownerMode innerRaw
                _ ->
                  Left "classifiedBy universe seed must expose a base constructor through unary wrappers"
        RPLit _ ->
          Left "literal is not allowed in classifiedBy universe"

    asModalityCall rawRef0 args0 =
      case (rtrMode rawRef0, rtrName rawRef0, args0) of
        (Nothing, name, [inner]) ->
          Just (RMComp [name], inner)
        (Just modeTok, name, [inner]) ->
          Just (RMComp [modeTok, name], inner)
        _ -> Nothing
