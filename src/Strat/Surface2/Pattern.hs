{-# LANGUAGE OverloadedStrings #-}
module Strat.Surface2.Pattern
  ( MVar(..)
  , PTerm(..)
  , PArg(..)
  , MetaSubst(..)
  , Subst2
  , NatSubst
  , MatchSubst(..)
  , matchPTerm
  , matchPTermWithSubst
  , matchPTermRigid
  , applySubstPTerm
  , resolvePlaceholders
  , instantiateMeta
  ) where

import Strat.Surface2.Term
import Data.Text (Text)
import qualified Data.Map.Strict as M
import qualified Data.List as L
import qualified Data.Text as T
import qualified Data.Set as S
import Control.Monad ((<=<))

newtype MVar = MVar Text
  deriving (Eq, Ord, Show)

data PTerm
  = PBound Ix
  | PBoundVar Text
  | PFree Text
  | PCon Con2Name [PArg]
  | PMeta MVar [Ix]
  deriving (Eq, Ord, Show)

data PArg = PArg
  { paBinders :: [PTerm]
  , paBody :: PTerm
  } deriving (Eq, Ord, Show)

data MetaSubst = MetaSubst
  { msArity :: Int
  , msBody :: STerm
  } deriving (Eq, Ord, Show)

type Subst2 = M.Map MVar MetaSubst
type NatSubst = M.Map Text Int

data MatchSubst = MatchSubst
  { msTerms :: Subst2
  , msNats :: NatSubst
  } deriving (Eq, Ord, Show)

matchPTerm :: PTerm -> STerm -> Either Text (Maybe MatchSubst)
matchPTerm = matchPTermWithSubst True (MatchSubst M.empty M.empty)

matchPTermRigid :: PTerm -> STerm -> Either Text (Maybe MatchSubst)
matchPTermRigid = matchPTermWithSubst False (MatchSubst M.empty M.empty)

matchPTermWithSubst :: Bool -> MatchSubst -> PTerm -> STerm -> Either Text (Maybe MatchSubst)
matchPTermWithSubst allowPlaceholders subst p t = go subst p t
  where
    isPlaceholder name = T.isPrefixOf (T.singleton '_') name
    placeholderName name = T.stripPrefix (T.singleton '_') name

    bindMeta mv ixs tm subst' =
      case M.lookup mv (msTerms subst') of
        Nothing -> do
          body <- abstract ixs tm
          Right (Just subst' { msTerms = M.insert mv (MetaSubst (length ixs) body) (msTerms subst') })
        Just ms -> do
          tm' <- instantiateMeta ms ixs
          if tm' == tm
            then Right (Just subst')
            else Right Nothing

    bindPlaceholder name tm subst' =
      case M.lookup (MVar name) (msTerms subst') of
        Nothing -> Right (Just subst' { msTerms = M.insert (MVar name) (MetaSubst 0 tm) (msTerms subst') })
        Just ms -> do
          tm' <- instantiateMeta ms []
          if tm' == tm then Right (Just subst') else Right Nothing

    go subst' pat tm =
      case pat of
        PBound ix ->
          case tm of
            SBound ix' | ix == ix' -> Right (Just subst')
            _ -> Right Nothing
        PBoundVar name ->
          case tm of
            SBound (Ix k) ->
              case M.lookup name (msNats subst') of
                Nothing -> Right (Just subst' { msNats = M.insert name k (msNats subst') })
                Just k' -> if k' == k then Right (Just subst') else Right Nothing
            _ -> Right Nothing
        PFree n ->
          case tm of
            SFree n' | n == n' -> Right (Just subst')
            _ -> Right Nothing
        PCon c args ->
          case tm of
            SFree name | allowPlaceholders && isPlaceholder name ->
              case placeholderName name of
                Nothing -> Right Nothing
                Just base -> do
                  tm' <- applySubstPTerm subst' pat
                  bindPlaceholder base tm' subst'
            SCon c' args' | c == c' && length args == length args' ->
              L.foldl' stepArg (Right (Just subst')) (zip args args')
            _ -> Right Nothing
        PMeta mv ixs ->
          case tm of
            SFree name
              | isPlaceholder name ->
                  if allowPlaceholders
                    then
                      case placeholderName name of
                        Just base | base == renderMVar mv -> Right (Just subst')
                        Just base -> do
                          tm' <- applySubstPTerm subst' pat
                          bindPlaceholder base tm' subst'
                        Nothing -> bindMeta mv ixs tm subst'
                    else Right Nothing
              | otherwise -> Right Nothing
            _ -> bindMeta mv ixs tm subst'

    goArg subst' (PArg pBinders pBody) (SArg sBinders sBody) =
      if length pBinders /= length sBinders
        then Right Nothing
        else do
          subst'' <- L.foldl' stepBinder (Right (Just subst')) (zip pBinders sBinders)
          case subst'' of
            Nothing -> Right Nothing
            Just s -> go s pBody sBody
    stepArg acc (pArg, tArg) =
      case acc of
        Left err -> Left err
        Right Nothing -> Right Nothing
        Right (Just s) -> goArg s pArg tArg

    stepBinder acc (pb, sb) =
      case acc of
        Left err -> Left err
        Right Nothing -> Right Nothing
        Right (Just s) -> go s pb sb

applySubstPTerm :: MatchSubst -> PTerm -> Either Text STerm
applySubstPTerm subst = resolvePlaceholders subst <=< go
  where
    metaPlaceholder name = "_" <> name
    go pat =
      case pat of
        PBound ix -> Right (SBound ix)
        PBoundVar name ->
          case M.lookup name (msNats subst) of
            Nothing -> Left "applySubstPTerm: unbound nat variable"
            Just k -> Right (SBound (Ix k))
        PFree n -> Right (SFree n)
        PCon c args -> SCon c <$> mapM goArg args
        PMeta mv ixs ->
          case M.lookup mv (msTerms subst) of
            Nothing ->
              let name = renderMVar mv
              in Right (SFree (metaPlaceholder name))
            Just ms ->
              instantiateMeta ms ixs

    goArg (PArg binders body) =
      SArg <$> mapM go binders <*> go body

resolvePlaceholders :: MatchSubst -> STerm -> Either Text STerm
resolvePlaceholders subst = go S.empty
  where
    go seen tm =
      case tm of
        SFree name ->
          case T.stripPrefix (T.singleton '_') name of
            Nothing -> Right tm
            Just base ->
              let alreadySeen = base `S.member` seen
                  lookupMeta =
                    case M.lookup (MVar base) (msTerms subst) of
                      Just ms -> Just (base, ms)
                      Nothing -> Nothing
              in
                if alreadySeen
                  then Right tm
                  else
                    case lookupMeta of
                      Nothing -> Right tm
                      Just (key, ms) ->
                        if msArity ms /= 0
                          then Right tm
                          else
                            case instantiateMeta ms [] of
                              Left err -> Left err
                              Right tm' ->
                                let seen' = S.insert base (S.insert key seen)
                                in go seen' tm'
        SBound _ -> Right tm
        SCon con args -> SCon con <$> mapM (goArg seen) args

    goArg seen (SArg binders body) =
      SArg <$> mapM (go seen) binders <*> go seen body

instantiateMeta :: MetaSubst -> [Ix] -> Either Text STerm
instantiateMeta ms ixs
  | msArity ms /= length ixs = Left "instantiateMeta: arity mismatch"
  | otherwise =
      let args = map SBound ixs
      in substMany args (msBody ms)

abstract :: [Ix] -> STerm -> Either Text STerm
abstract ixs tm = do
  let k = length ixs
  shifted <- shift k 0 tm
  let mapping = M.fromList [ (ixKey ix, idx) | (idx, ix) <- zip [0..] ixs ]
  pure (replaceBound mapping 0 shifted)
  where
    ixKey (Ix i) = i + length ixs

replaceBound :: M.Map Int Int -> Int -> STerm -> STerm
replaceBound mapping depth tm =
  case tm of
    SBound (Ix k) ->
      let absIx = k + depth
      in case M.lookup absIx mapping of
           Nothing -> SBound (Ix k)
           Just paramIx -> SBound (Ix (paramIx + depth))
    SFree t -> SFree t
    SCon con args ->
      SCon con (map (replaceArg mapping depth) args)

replaceArg :: M.Map Int Int -> Int -> SArg -> SArg
replaceArg mapping depth (SArg binders body) =
  let binders' = map (replaceBound mapping depth) binders
      body' = replaceBound mapping (depth + length binders) body
  in SArg binders' body'

renderMVar :: MVar -> Text
renderMVar (MVar t) = t
