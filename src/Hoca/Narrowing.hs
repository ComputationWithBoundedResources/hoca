{-# LANGUAGE ViewPatterns #-}
-- | 

module Hoca.Narrowing (
  NarrowedRule (..)
  , Narrowing (..)
  , narrow
  ) where

import qualified Data.Rewriting.Context as C
import qualified Data.Rewriting.Rule as R
import qualified Data.Rewriting.Substitution as S
import           Data.Rewriting.Substitution.Unify (unify)
import qualified Data.Rewriting.Term as T
import Control.Monad (guard)
import Data.Maybe (catMaybes, mapMaybe)

data NarrowedRule f v =
  NarrowedRule {
    narrowedRule :: R.Rule f v
    , narrowCtxt :: C.Ctxt f v
    , narrowSubterm :: T.Term f v 
    , narrowings :: [Narrowing f v]
    } deriving (Show)

data Narrowing f v =
  Narrowing {
    narrowingMgu :: S.Subst f v 
    , narrowedWith :: R.Rule f v
    , narrowing :: R.Rule f v
    } deriving (Show)

-- | @(C,s) `elem` contexts t@ if and only if @t = C[s]@.
contexts :: T.Term f v -> [(C.Ctxt f v, T.Term f v)]
contexts = walk id
  where
    walk c s@(T.Var _) = [(c C.Hole,s)]
    walk c s@(T.Fun f ss) =
      (c C.Hole, s) : concatMap (\ (ls,si,rs) -> walk (\ ctxt -> c (C.Ctxt f ls ctxt rs)) si) (parts [] ss)

    parts _ [] = []
    parts ls (t:rs) = (ls,t,rs) : parts (ls ++ [t]) rs

narrow :: (Eq f, Ord v1, Ord v2) => R.Rule f v1 -> [R.Rule f v2] -> [NarrowedRule f (Either v1 v2)]
narrow rl rs = catMaybes [ narrowAt ci ri | (ci,ri) <- contexts rhs, T.isFun ri ]
  where
    lhs = T.rename Left `R.left` rl
    rhs = T.rename Left `R.right` rl
    
    narrowAt ci ri = do
      let ns = mapMaybe (narrowWith ci ri . R.rename Right) rs
      guard (not (null ns))
      return NarrowedRule {
        narrowedRule = R.Rule lhs rhs
        , narrowCtxt = ci
        , narrowSubterm = ri
        , narrowings = ns }

    narrowWith ci ri rli = do
        mgu <- unify ri (R.lhs rli)
        let lhs' = S.apply mgu lhs
            rhs' = S.applyCtxt mgu ci `C.apply` S.apply mgu (R.rhs rli)
        return Narrowing { narrowingMgu = mgu
                         , narrowedWith = rli
                         , narrowing = R.Rule lhs' rhs' }