-- | 

module Hoca.Transform (
  pcfToTrs
  -- * Simplifications
  , usableRules
  , neededRules
  , uncurryRules
  -- , etaSaturateRules
  , compress
  -- , arglabel
  , dfaInstantiate
    -- ** Rule Narrowing
  , narrow
  , rewrite
  , complexityPreserving
  , complexityReflecting
)
       where

import           Control.Applicative (empty, pure, (<$>))
import           Data.List (nub)
import qualified Data.Map as Map
import           Data.Maybe (listToMaybe, isNothing, fromMaybe)
import qualified Data.MultiSet as MS

import           Data.Rewriting.Substitution (unify, apply)
import           Data.Rewriting.Applicative.Term (aterm, atermM, AView (..), ASym (..), fun, app)
import qualified Data.Rewriting.Applicative.SimpleTypes as ST
import qualified Data.Rewriting.Applicative.Term  as T
import qualified Data.Rewriting.Applicative.Rule as R
import qualified Data.Rewriting.Applicative.Rules as RS
import qualified Data.Rewriting.Term  as Term

import qualified Hoca.Data.TreeGrammar as TG
import qualified Hoca.DFA as DFA
import Hoca.PCF.Sugar.Types (Context)
import qualified Hoca.Narrowing as N
import qualified Hoca.Uncurry as UC
import           Hoca.PCF.Core (Exp)
import qualified Hoca.PCF2Atrs as PCF2Atrs
import           Hoca.Problem (Symbol (..), Problem)
import qualified Hoca.Problem as Problem
import qualified Hoca.UsableRules as UR

import Hoca.Strategy
import Data.Maybe (catMaybes)
import Data.List (intersect)

-- Transformations

pcfToTrs :: Exp Context :~> Problem Symbol Int
pcfToTrs = pure . PCF2Atrs.toProblem

reducibleVars :: (Ord f, Ord v) => Problem f v -> N.Narrowing (ASym f) v v -> [v]
reducibleVars p n =
  [ v | v <- nub (T.vars (R.lhs rl))
      , any isCall (T.subterms ( mgu `apply` T.var (Right v))) ]
  where
    rl = N.narrowedWith n    
    mgu = N.narrowingMgu n
    isCall (aterm -> Var _)  = False
    isCall (aterm -> (_ :@ _)) = True
    isCall (aterm -> Fun f _) = f `elem` ds
    isCall _ = error "Hoca.Transform.normalisedVars match failure"
    ds = [ f | Fun f _ <- map aterm (RS.lhss (Problem.rules p)) ]
    
complexityReflecting :: (Ord f, Ord v) => Problem f v -> N.NarrowedRule (ASym f) v v -> Bool
complexityReflecting p nr = all redexPreserving (N.narrowings nr) where
  redexPreserving n = varsMS (R.lhs rl) == varsMS (R.rhs rl) where
    rl = N.narrowedWith n
    varsMS = MS.fromList . filter (`elem` withCall) . T.vars
    withCall = reducibleVars p n

complexityPreserving :: (Ord f, Ord v) => Problem f v -> N.NarrowedRule (ASym f) v v -> Bool
complexityPreserving p nr = all redexReflecting (N.narrowings nr) where
  redexReflecting n = varsMS (R.rhs rl) `MS.isSubsetOf` varsMS (R.lhs rl) where
    rl = N.narrowedWith n
    varsMS = MS.fromList . filter (`elem` withCall) . T.vars
    withCall = reducibleVars p n

narrow :: (Ord f, Ord v, Num v) => (Problem f v -> N.NarrowedRule (ASym f) v v -> Bool) -> Problem f v :~> Problem f v
narrow sensible p = Problem.replaceRulesM narrowRule p where
  renameRule = R.rename ren where
     ren (Left v) = v * 2 + 1
     ren (Right v) = v * 2
  
  narrowRule i rl ss = 
    case listToMaybe [ ni | ni <- N.narrow rl rules, complexityReflecting p ni, sensible p ni ] of
     Nothing -> empty
     Just ni -> return [(renameRule (N.narrowing n)
                         , ss ++ Problem.cgSuccs p nidx )
                       | n <- N.narrowings ni
                       , let nidx = fromMaybe (error "narrow rule id not found") (lookup (N.narrowedWith n) rulesE)
                       ]
     where 
       rulesE = [ (rl',j) | j <- Problem.cgSuccs p i, Just rl' <- [Problem.rule p j] ]
       rules = map fst rulesE

rewrite :: (Ord f, Ord v, Num v) => (Problem f v -> N.NarrowedRule (ASym f) v v -> Bool) -> Problem f v :~> Problem f v
rewrite sensible = narrow sensible' where
  sensible' rs nr = all (\ nw -> R.lhs (N.narrowedRule nr) `T.isVariantOf` R.lhs (N.narrowing nw)) (N.narrowings nr)
                    && sensible rs nr
  
usableRules :: Ord v => Problem Symbol v :~> Problem Symbol v
usableRules p
  | Problem.size p' < Problem.size p = pure p'
  | otherwise = empty
  where
    p' = Problem.removeUnusedRules (Problem.withEdges edgeP p)
    rs = Problem.rules p
    r1 `edgeP` r2 = maybe False (elem r2) (lookup r1 ss)
    ss = [(r,UR.calls (R.rhs r) rs) | r <- rs ]

neededRules :: Ord v => Problem Symbol v :~> Problem Symbol v
neededRules p = Problem.replaceRulesM (\ _ rl _ -> if needed rl then empty else pure []) p where
  needed rl =
    case T.headSymbol (R.lhs rl) of
     Just (l@Lambda {}) -> l `elem` createdFuns
     Just (l@Fix {}) -> l `elem` createdFuns
     _ -> True
  createdFuns = foldr T.funsDL [] (RS.rhss (Problem.rules p))

dfaInstantiate :: (ST.ATypedRule Symbol Int -> Int -> [T.ATerm Symbol ()] -> Bool) -> Problem Symbol Int :~> Problem Symbol Int
dfaInstantiate refineP prob = 
  case ST.inferTypes rs of
   Left _ -> empty
   Right (sig,ers) -> Problem.replaceRulesM replace prob where
     replace i rl ss
       | changed = Just replacements
       | otherwise = Nothing
       where
         replacements = [(rl',succs) | rl' <- rs', argumentNormalised (R.lhs rl')] where
           (rs',succs) = mkRefinements i refineP'
           refineP' = maybe (const (const False)) (refineP . fst) (lookup i ers)
           
         changed =
           case replacements of
            [(rl',succs)] -> any (`notElem` succs) ss
                             || R.lhs rl `properInstOf` R.lhs rl'
            _ -> True
           
     initialDFA = TG.fromList (startRules ++ constructorRules) where
       startRules = 
         [ TG.Production DFA.startNonTerminal (TG.Terminal (Sym f) [TG.NonTerminal (DFA.auxNonTerminal t) | t <- ST.inputTypes td])
         | (f, td) <- Map.toList sig, Problem.isMainSym f]
       constructorRules = 
         [ TG.Production (DFA.auxNonTerminal (ST.outputType td)) (TG.Terminal (Sym c) [TG.NonTerminal (DFA.auxNonTerminal t) | t <- ST.inputTypes td])
         | (c, td) <- Map.toList sig, Problem.isConstructor c ]
           
     mkRefinements = DFA.refinements rs initialDFA

     argumentNormalised t = all norm (T.properSubterms t) where
       norm (atermM -> Just (T.Var _)) = True
       norm (atermM -> Just (_ :@ _)) = False
       norm li = all (isNothing . unify li) (RS.lhss (map snd rs))

     Term.Var {} `properInstOf` Term.Fun {} = True
     (Term.Fun _ ts) `properInstOf` (Term.Fun _ ss) = or (zipWith properInstOf ts ss)
     _ `properInstOf` _ = False
       
  where rs = Problem.rulesEnum prob

uncurryRules :: Problem Symbol Int :~> Problem Symbol Int
uncurryRules p = Problem.fromRules <$> UC.uncurried (Problem.rules p)

compress :: Problem Symbol Int :~> Problem Symbol Int
compress p = Problem.replaceRulesM replace p where
  replace _ rl ss = Just [(R.mapRule compressTerm rl,ss)]
  compressTerm (aterm -> Fun f ts) =
    case Map.lookup f cm of
     Just as -> fun f (catMaybes (zipWith cti as ts))
     Nothing -> fun f (map compressTerm ts)
  compressTerm (aterm -> t1 :@ t2) = compressTerm t1 `app` compressTerm t2
  compressTerm t = t
  cti Nothing    ti = Just (compressTerm ti)
  cti (Just _) _ = Nothing 
  
  cm = foldl ins Map.empty (concatMap T.subterms terms) where
    ins m (aterm -> Fun f ts) = Map.alter alter f m where
      alter Nothing = Just (map (\ ti -> if T.isGround ti then Just ti else Nothing) ts)
      alter (Just ts') = Just (zipWith combine ts' ts)
      combine Nothing _ = Nothing
      combine (Just ti') ti
        | ti' == ti && T.isGround ti = Just ti
        | otherwise = Nothing
    ins m _ = m
  terms = RS.lhss rs ++ RS.rhss rs
  rs = Problem.rules p

