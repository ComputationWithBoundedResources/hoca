{-# LANGUAGE ScopedTypeVariables #-}
-- | 

module Hoca.UsableRules (
  usableRules
  ) where

import qualified Data.Rewriting.Rule as R
import qualified Data.Rewriting.Rules as RS
import qualified Data.Rewriting.Term as T
import           Data.List (partition)
import Control.Monad.State.Lazy as State
import Control.Applicative ((<$>))
import Data.Rewriting.Substitution.Unify (unify)
import Data.Maybe (isJust)


-- assumes that variables are disjoint
isUnifiableWith :: (Ord v1, Ord v2, Eq f) => T.Term f v1 -> T.Term f v2 -> Bool
isUnifiableWith t1 t2 = isJust (unify (T.rename Left t1) (T.rename Right t2))

-- cap f(t1,...,tn) == f(tcap(t1),...,tcap(tn))
cap :: (Eq f, Ord v1, Ord v2) => [R.Rule f v1] -> T.Term f v2 -> T.Term f Int
cap rs t = State.evalState (capM t) 0 
  where
    lhss = RS.lhss rs

    freshVar :: State.State Int (T.Term f Int)
    freshVar = State.modify succ >> (T.Var <$> State.get)

    capM (T.Var _) = freshVar
    capM (T.Fun f ts) = T.Fun f <$> mapM tcapM ts
    
    tcapM (T.Var _) = freshVar
    tcapM (T.Fun f ts) = do 
      s <- T.Fun f <$> mapM tcapM ts
      if any (isUnifiableWith s) lhss
       then freshVar
       else return s

usableRules :: (Eq f, Ord v1, Ord v2) => [T.Term f v1] -> [R.Rule f v2] -> [R.Rule f v2]
usableRules ts rules = walk (caps ts) [] rules
  where
    walk []     ur _  = ur
    walk (s:ss) ur rs = walk (caps (RS.rhss ur') ++ ss) (ur' ++ ur) rs'
      where
        (ur',rs') = partition (\ rl -> s `isUnifiableWith` R.lhs rl) rs
    caps ss = [ cap rules s | si <- ss, s@T.Fun{} <- T.subterms si ]    
