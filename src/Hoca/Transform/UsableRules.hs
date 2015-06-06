{-# LANGUAGE NoMonomorphismRestriction #-}

module Hoca.Transform.UsableRules (
  usableRulesSyntactic
  , usableRulesDFA
  , usableRulesDFA'
  , isRecursive
  , calls
  ) where

import           Control.Applicative (empty)
import           Control.Monad (guard)
import           Data.Function (on)
import           Data.List (partition)
import           Data.Maybe (isJust)
import qualified Data.Rewriting.Rule as R
import qualified Data.Rewriting.Rules as RS
import           Data.Rewriting.Substitution.Unify (unify)
import qualified Data.Rewriting.Term as T
import qualified Hoca.Data.TreeGrammar as TG
import           Hoca.Problem
import           Hoca.Problem.DFA
import           Hoca.Strategy
import           Hoca.Transform.Defunctionalize (Symbol (..), unlabeled)
import           Hoca.Utils (runVarSupply, fresh)

-- assumes that variables are disjoint
isUnifiableWith :: (Ord v1, Ord v2, Eq f) => T.Term f v1 -> T.Term f v2 -> Bool
isUnifiableWith t1 t2 = isJust (unify (T.rename Left t1) (T.rename Right t2))

-- cap f(t1,...,tn) == f(tcap(t1),...,tcap(tn))
cap :: (Eq f, Ord v1, Ord v2) => [R.Rule f v2] -> T.Term f v1 -> T.Term f Int
cap rs t = runVarSupply (capM t)
  where
    freshVar = T.Var <$> fresh
    lhss = RS.lhss rs

    capM (T.Var _) = freshVar
    capM (T.Fun f ts) = T.Fun f <$> mapM tcapM ts
    
    tcapM (T.Var _) = freshVar
    tcapM (T.Fun f ts) = do 
      s <- T.Fun f <$> mapM tcapM ts
      if any (isUnifiableWith s) lhss then freshVar else return s

calls :: (Eq f, Ord v1, Ord v2) => T.Term f v1 -> [R.Rule f v2] -> [R.Rule f v2]
calls t trs = concatMap (\ ti -> filter (\ rl -> ti `isUnifiableWith` R.lhs rl) trs) caps
  where caps = [ cap trs ti | ti@T.Fun{} <- T.subterms t ]    

usableFor :: (Eq f, Ord v1, Ord v2) => [T.Term f v1] -> [R.Rule f v2] -> [R.Rule f v2]
usableFor ts trs = walk (caps trs ts) [] trs
  where
    walk []     ur _  = ur
    walk (s:ss) ur rs = walk (caps trs (RS.rhss ur') ++ ss) (ur' ++ ur) rs' where
        (ur',rs') = partition (\ rl -> s `isUnifiableWith` R.lhs rl) rs
    caps rs ss = [ cap rs s | si <- ss, s@T.Fun{} <- T.subterms si ]    

    
isRecursive :: (Ord v1, Ord v2, Eq f) => [R.Rule f v1] -> R.Rule f v2 -> Bool
isRecursive rs rl =
  any (R.isVariantOf rl) (usableFor [R.rhs rl] rs)

usableRulesSyntactic :: (Eq f, Ord v) => Problem f v :=> Problem f v
usableRulesSyntactic p
  | size p' < size p = pure p'
  | otherwise = empty
  where
    p' = removeUnusedRules (withEdges (edgeP `on` theRule) p)
    rs = theRule `map` rules p
    r1 `edgeP` r2 = maybe False (elem r2) (lookup r1 ss)
    ss = [(r,calls (R.rhs r) rs) | r <- rs ]

usableRulesDFA' :: (Ord f) => (f -> Bool) -> Problem f Int :=> Problem f Int
usableRulesDFA' isData prob = replaceRulesIdx replace prob where
    tg = dfa isData prob
  
    reachableRules = concatMap TG.nonTerminals . TG.produces tg
  
    replace idx trl succs = guard changed >> Just [(trl,newSuccs)]
      where
        changed = any (`notElem` newSuccs) succs
        newSuccs = [j | (R j) <- reachableRules (R idx) ]

usableRulesDFA :: Problem Symbol Int :=> Problem Symbol Int
usableRulesDFA = usableRulesDFA' isData where
   isData (unlabeled -> (Con {})) = True
   isData _ = False 
