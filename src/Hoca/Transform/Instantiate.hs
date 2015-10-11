module Hoca.Transform.Instantiate (
  RefineP
  , instantiate
  , instantiate'
  -- refinement predicates
  , refineND
  , refineHOVars
  , orRefine
) where

import           Control.Monad (guard)
import qualified Data.List as L
import qualified Data.Map as M
import           Data.Maybe (fromJust, isNothing)
import qualified Data.Rewriting.Applicative.Rule as R
import qualified Data.Rewriting.Applicative.Term as T
import           Data.Rewriting.Substitution (unify)
import qualified Data.Rewriting.Substitution as S
import qualified Data.Rewriting.Substitution.Type as ST
import qualified Hoca.Data.TreeGrammar as TG
import           Hoca.Problem
import           Hoca.Data.MLTypes (Type)
import           Hoca.Problem.DFA
import           Hoca.Strategy
import qualified Hoca.Data.MLTypes as TP
import           Hoca.Utils (runVarSupply, fresh)

type RefineP f = TRule f Int -> Int -> [T.ATerm f ()] -> Bool

instantiate :: (Ord f) => RefineP f -> Problem f Int :=> Problem f Int
instantiate refineP prob = snd <$> instantiate' refineP prob

instantiate' :: (Ord f) => RefineP f -> Problem f Int :=> (DFAGrammar f Int Type, Problem f Int)
instantiate' refineP prob = (,) tg <$> replaceRulesIdx replace prob where
  tg = dfa prob

  sig = signature prob

  reducts s =
    case TG.produces' tg s of 
     [] -> [TG.NonTerminal s]
     rhss -> rhss

  reachableRules = concatMap TG.nonTerminals . TG.produces tg
  
  apply s t = fromJust (S.gApply s t)
  
  lhss = leftHandSides prob
  
  toSubst = ST.fromMap . M.fromList . runVarSupply . mapM (\ (v,p) -> (,) v <$> ren p)
    where
      ren (T.Fun f ts) = T.Fun f <$> mapM ren ts
      ren _            = T.Var <$> fresh

  argumentNormalised t = all norm (T.properSubterms t) where
    norm (T.Var _) = True      
    norm (T.atermM -> Just (_ T.:@ _)) = False
    norm li = all (isNothing . unify li) lhss

  T.Var {} `properInstOf` T.Fun {} = True
  (T.Fun _ ts) `properInstOf` (T.Fun _ ss) = or (zipWith properInstOf ts ss)
  _ `properInstOf` _ = False

  replace idx trl succs = guard changed >> Just [(trl',newSuccs) | trl' <- newRules] where
    R.Rule lhs rhs = theRule trl
    vars = L.nub (T.vars lhs)
    changed = 
      case newRules of 
       [trl'] -> any (`notElem` newSuccs) succs || lhs `properInstOf` R.lhs (theRule trl')
       _ -> True

    newRules = [ trl' | s <- substs
                      , let lhs' = s `apply` lhs
                      , let rhs' = s `apply` rhs
                      , argumentNormalised lhs'
                      , Right trl' <- [inferWith sig [] (R.Rule lhs' rhs')]]

    newSuccs = [j | (R j) <- reachableRules (R idx) ]

    substs = map toSubst (foldl (\ l v -> [ (v,p):s | s <- l, p <- patterns v]) [[]] vars) where 
        patterns v
          | refineP trl v assigns = assigns
          | otherwise = [T.Var ()]
          where assigns = L.nub (map unliftTerm (reducts (V v idx)))


-- refinements
---------------------------------------------------------------------- 

orRefine :: RefineP f -> RefineP f -> RefineP f
orRefine r1 r2 = \ trl v ps -> r1 trl v ps || r2 trl v ps

-- * non-deterministic refinement, this will not duplicate rules
refineND :: RefineP f
refineND _ _ []  = True
refineND _ _ [_] = True
refineND _ _ _   = False

-- * refine all higher-order variables, i.e. those substitutable by functions
refineHOVars :: Eq f => RefineP f
refineHOVars trl v _ = 
    maybe False TP.isTArrow (lookup v (theEnv trl)) 
    && (T.var v == r || v `elem` T.headVars r) 
    where
      r = R.rhs (theRule trl)

