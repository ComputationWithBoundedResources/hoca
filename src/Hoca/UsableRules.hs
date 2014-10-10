{-# LANGUAGE ScopedTypeVariables #-}
-- | 

module Hoca.UsableRules (
  icap
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

-- ruleDefines :: Eq f => [f] -> R.Rule f v -> Bool
-- ruleDefines fs = either (const True) (`elem` fs) . T.root . R.lhs

isUnifiableWith :: (Ord v, Eq f) => T.Term f v -> T.Term f v -> Bool
isUnifiableWith t1 t2 = isJust (unify t1 t2)

icap :: (Eq f, Ord v1, Ord v2) => [R.Rule f v1] -> T.Term f v2 -> T.Term f (Either v2 Int)
icap rs t = State.evalState (tcapM (T.rename Left t)) 0 
  where
    lhss = map (T.rename (Left . Right)) (RS.lhss rs)

    freshVar :: State.State Int (Either v Int)
    freshVar = State.modify succ >> Right <$> State.get
    
    tcapM v@(T.Var _) = return v
    tcapM (T.Fun f ts) = do
      s <- T.Fun f <$> mapM tcapM ts
      let s' = T.rename (either (Left . Left) Right) s
      if any (isUnifiableWith s') lhss
       then T.Var <$> freshVar
       else return s


usableRules :: (Eq f, Ord v1, Ord v2) => [T.Term f v1] -> [R.Rule f v2] -> [R.Rule f v2]
usableRules ts = walk [ t | ti <- map (T.rename (Left . Left)) ts
                          , t <- T.subterms ti, T.isFun t] []
  where
    walk []     ur _  = ur
    walk (s:ss) ur rs = walk (ss' ++ ss) (ur' ++ ur) rs'
      where
        (ur',rs') = partition (\ rl -> s `isUnifiableWith` T.rename (Left . Right) (R.lhs rl)) rs
        ss' = [ icap rs' st | t <- map (T.rename Right) (RS.rhss ur')
                            , st <- T.subterms t, T.isFun st ]

      -- if null usable then fs' else walk (usableSyms' usable `union` fs') nonusable
      -- where (usable, nonusable) = partition (ruleDefines fs') rs2

-- | @usableRules rs rs2@ returns @rs2@ restricted to rules usable by @rs@
-- usableRules :: (Show f, Eq f) => [R.Rule f v] -> [R.Rule f v] -> [R.Rule f v]
-- usableRules rs rs2 = filter (ruleDefines (usableSyms fs rs2)) rs2
--   where fs = foldr T.funsDL [] (RS.rhss rs)

-- withUsableRules :: (Show f, Eq f) => [R.Rule f v] -> [R.Rule f v] -> [R.Rule f v]
-- withUsableRules rs rs2 = rs ++ usableRules rs rs2
