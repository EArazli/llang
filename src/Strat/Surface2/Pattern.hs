module Strat.Surface2.Pattern
  ( MVar(..)
  , PTerm(..)
  , PArg(..)
  , MetaSubst(..)
  , Subst2
  , NatSubst
  , MatchSubst(..)
  , matchPTerm
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

matchPTerm :: PTerm -> STerm -> Maybe MatchSubst
matchPTerm p t = go (MatchSubst M.empty M.empty) p t
  where
    isPlaceholder name = T.isPrefixOf (T.singleton '_') name
    placeholderName name = T.stripPrefix (T.singleton '_') name

    bindMeta mv ixs tm subst =
      case M.lookup mv (msTerms subst) of
        Nothing ->
          let body = abstract ixs tm
          in Just subst { msTerms = M.insert mv (MetaSubst (length ixs) body) (msTerms subst) }
        Just ms -> do
          tm' <- instantiateMeta ms ixs
          if tm' == tm
            then Just subst
            else Nothing

    bindPlaceholder name tm subst =
      case M.lookup (MVar name) (msTerms subst) of
        Nothing -> Just subst { msTerms = M.insert (MVar name) (MetaSubst 0 tm) (msTerms subst) }
        Just ms -> do
          tm' <- instantiateMeta ms []
          if tm' == tm then Just subst else Nothing

    go subst pat tm =
      case pat of
        PBound ix ->
          case tm of
            SBound ix' | ix == ix' -> Just subst
            _ -> Nothing
        PBoundVar name ->
          case tm of
            SBound (Ix k) ->
              case M.lookup name (msNats subst) of
                Nothing -> Just subst { msNats = M.insert name k (msNats subst) }
                Just k' -> if k' == k then Just subst else Nothing
            _ -> Nothing
        PFree n ->
          case tm of
            SFree n' | n == n' -> Just subst
            _ -> Nothing
        PCon c args ->
          case tm of
            SFree name | isPlaceholder name ->
              case placeholderName name of
                Nothing -> Nothing
                Just base -> bindPlaceholder base (applySubstPTerm subst pat) subst
            SCon c' args' | c == c' && length args == length args' ->
              L.foldl' (\acc (pArg, tArg) -> acc >>= \s -> goArg s pArg tArg) (Just subst) (zip args args')
            _ -> Nothing
        PMeta mv ixs ->
          case tm of
            SFree name | isPlaceholder name ->
              case placeholderName name of
                Just base | base == renderMVar mv -> Just subst
                _ -> bindMeta mv ixs tm subst
            _ -> bindMeta mv ixs tm subst

    goArg subst (PArg pBinders pBody) (SArg sBinders sBody) =
      if length pBinders /= length sBinders
        then Nothing
        else do
          subst' <- L.foldl' (\acc (pb, sb) -> acc >>= \s -> go s pb sb) (Just subst) (zip pBinders sBinders)
          go subst' pBody sBody

applySubstPTerm :: MatchSubst -> PTerm -> STerm
applySubstPTerm subst = resolvePlaceholders subst . go
  where
    go pat =
      case pat of
        PBound ix -> SBound ix
        PBoundVar name ->
          case M.lookup name (msNats subst) of
            Nothing -> error "applySubstPTerm: unbound nat variable"
            Just k -> SBound (Ix k)
        PFree n -> SFree n
        PCon c args -> SCon c (map goArg args)
        PMeta mv ixs ->
          case M.lookup mv (msTerms subst) of
            Nothing ->
              let name = renderMVar mv
                  prefix = T.singleton '_'
              in SFree (if T.isPrefixOf prefix name then name else prefix <> name)
            Just ms ->
              case instantiateMeta ms ixs of
                Nothing -> error "applySubstPTerm: arity mismatch"
                Just tm -> tm

    goArg (PArg binders body) =
      SArg (map go binders) (go body)

resolvePlaceholders :: MatchSubst -> STerm -> STerm
resolvePlaceholders subst = go S.empty
  where
    go seen tm =
      case tm of
        SFree name ->
          case T.stripPrefix (T.singleton '_') name of
            Nothing -> tm
            Just base ->
              if base `S.member` seen
                then tm
                else
                  case M.lookup (MVar base) (msTerms subst) of
                    Nothing -> tm
                    Just ms ->
                      if msArity ms /= 0
                        then tm
                        else
                          case instantiateMeta ms [] of
                            Nothing -> tm
                            Just tm' -> go (S.insert base seen) tm'
        SBound _ -> tm
        SCon con args -> SCon con (map (goArg seen) args)

    goArg seen (SArg binders body) =
      SArg (map (go seen) binders) (go seen body)

instantiateMeta :: MetaSubst -> [Ix] -> Maybe STerm
instantiateMeta ms ixs
  | msArity ms /= length ixs = Nothing
  | otherwise =
      let args = map SBound ixs
          body' = substMany args (msBody ms)
      in Just body'

abstract :: [Ix] -> STerm -> STerm
abstract ixs tm =
  let k = length ixs
      shifted = shift k 0 tm
      mapping = M.fromList [ (ixKey ix, idx) | (idx, ix) <- zip [0..] ixs ]
  in replaceBound mapping 0 shifted
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
