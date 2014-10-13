{-# LANGUAGE ScopedTypeVariables #-}
-- | 

module Hoca.UsableRules (
  tcap
  , usableRules
  ) where

import qualified Data.Rewriting.Rule as R
import qualified Data.Rewriting.Rules as RS
import qualified Data.Rewriting.Term as T
import           Data.List (partition)
import Control.Monad.State.Lazy as State
import Control.Applicative ((<$>))
import Data.Rewriting.Substitution.Unify (unify)
import Data.Maybe (isJust)

isUnifiableWith :: (Ord v, Eq f) => T.Term f v -> T.Term f v -> Bool
isUnifiableWith t1 t2 = isJust (unify t1 t2)

tcap :: (Eq f, Ord v1, Ord v2) => [R.Rule f v1] -> T.Term f v2 -> T.Term f (Either v2 Int)
tcap rs t = State.evalState (tcapM (T.rename Left t)) 0 
  where
    lhss = map (T.rename (Left . Right)) (RS.lhss rs)

    freshVar :: State.State Int (Either v Int)
    freshVar = State.modify succ >> Right <$> State.get
    
    tcapM (T.Var _) = T.Var <$> freshVar
    tcapM (T.Fun f ts) = do
      s <- T.Fun f <$> mapM tcapM ts
      let s' = T.rename (either (Left . Left) Right) s
      if any (isUnifiableWith s') lhss
       then T.Var <$> freshVar
       else return s


usableRules :: (Eq f, Ord v1, Ord v2) => [T.Term f v1] -> [R.Rule f v2] -> [R.Rule f v2]
usableRules ts rules = walk [ T.Fun f (map (tcap rules) tis)
                            | ti <- map (T.rename Left) ts
                            , T.Fun f tis <- T.subterms ti]
                       [] rules
  where
    walk []     ur _  = ur
    walk (s:ss) ur rs = walk (ss' ++ ss) (ur' ++ ur) rs'
      where
        (ur',rs') = partition (\ rl -> s `isUnifiableWith` T.rename (Left . Right) (R.lhs rl)) rs
        ss' = [ T.Fun f (map (tcap rules) uis)
              | u <- map (T.rename Right) (RS.rhss ur')
              , T.Fun f uis <- T.subterms u ]
