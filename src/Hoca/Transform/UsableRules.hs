module Hoca.Transform.UsableRules (
  usableRulesSyntactic
  , usableRulesDFA
  ) where

import           Control.Monad (guard)
import           Data.Maybe (isJust)
import qualified Data.Rewriting.Rule as R
import qualified Data.Rewriting.Rules as RS
import           Data.Rewriting.Substitution.Unify (unify)
import qualified Data.Rewriting.Term as T
import qualified Hoca.Data.TreeGrammar as TG
import           Hoca.Problem
import           Hoca.Problem.DFA
import           Hoca.Strategy
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

usableRulesGeneric :: (Ord f, Ord v) => (Int -> TRule f v -> [Int] -> [Int]) -> Problem f v :=> Problem f v
usableRulesGeneric urs = replaceRulesIdx replace where
    replace idx trl succs = guard changed >> Just [(trl,newSuccs)] 
        where
          changed = any (`notElem` newSuccs) succs
          newSuccs = urs idx trl succs
    
    
usableRulesSyntactic :: (Ord f, Ord v) => Problem f v :=> Problem f v
usableRulesSyntactic p = usableRulesGeneric urs p where
    urs _ (R.rhs . theRule -> r) = filter f
        where f (rule p -> Just trl) = or [c `isUnifiableWith` R.lhs (theRule trl) | c <- caps r]
              f _                    = error "usable rules: rule not found in problem"
    caps t = [cap rs ti | ti@T.Fun{} <- T.subterms t]
    rs = theRule `map` rules p

usableRulesDFA :: (Ord f, Ord v) => Problem f v :=> Problem f v
usableRulesDFA p = usableRulesGeneric urs p where
    tg = dfa p
    reachableRules = concatMap TG.nonTerminals . TG.produces tg
    urs idx _ succs = [j | (R j) <- reachableRules (R idx), j `elem` succs ]
  

