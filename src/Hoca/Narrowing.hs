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
import Hoca.Utils
import Data.Maybe (catMaybes, mapMaybe)

data NarrowedRule f v1 v2 =
  NarrowedRule {
    narrowedRule :: R.Rule f v1
    , narrowCtxt :: C.Ctxt f v1
    , narrowSubterm :: T.Term f v1 
    , narrowings :: [Narrowing f v1 v2]
    } deriving (Show)

data Narrowing f v1 v2 =
  Narrowing {
    narrowingMgu :: S.Subst f (Either v1 v2)
    , narrowedWith :: R.Rule f v2
    , narrowing :: R.Rule f (Either v1 v2)
    } deriving (Show)


renameCtx :: (v1 -> v2) -> C.Ctxt f v1 -> C.Ctxt f v2
renameCtx _ C.Hole = C.Hole
renameCtx fn (C.Ctxt f ts1 c ts2) = C.Ctxt f (map (T.rename fn) ts1) (renameCtx fn c) (map (T.rename fn) ts2)


narrow :: (Eq f, Ord v1, Ord v2) => R.Rule f v1 -> [R.Rule f v2] -> [NarrowedRule f v1 v2]
narrow rl rs = catMaybes [ narrowAt ci ri | (ci,ri) <- contexts (R.rhs rl), T.isFun ri ]
  where
    narrowAt ci ri = do
      let ns = mapMaybe (narrowWith ci ri) rs
      guard (not (null ns))
      return NarrowedRule {
        narrowedRule = rl
        , narrowCtxt = ci
        , narrowSubterm = ri
        , narrowings = ns }

    narrowWith ci ri rli = do
        mgu <- unify (T.rename Left ri) (T.rename Right (R.lhs rli))
        let ci' = renameCtx Left ci
            lhs' = S.apply mgu (T.rename Left (R.lhs rl))
            rhs' = S.applyCtxt mgu ci' `C.apply` S.apply mgu (T.rename Right (R.rhs rli))
        return Narrowing { narrowingMgu = mgu
                         , narrowedWith = rli
                         , narrowing = R.Rule lhs' rhs'
                         }
    
