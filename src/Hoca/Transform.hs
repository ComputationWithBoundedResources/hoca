-- | 

module Hoca.Transform (
  pcfToTrs
  -- * Simplifications
  , usableRules
  , neededRules
  , uncurryRules
  , etaSaturateRules
  , compress
  , arglabel
  , dfaInstantiate
    -- ** Rule Narrowing
  , narrow
  , rewrite
  , complexityPreserving
  , complexityReflecting
)
       where

import           Control.Applicative (empty, pure, (<$>))
import qualified Data.Map as Map
import           Data.List (nub)
import           Data.Maybe (listToMaybe, isNothing, fromMaybe)
import qualified Data.MultiSet as MS
import qualified Data.Rewriting.Rule as R
import qualified Data.Rewriting.Rules as RS
import           Data.Rewriting.Substitution (unify, apply)
import qualified Data.Rewriting.Term as T
import qualified Hoca.ATRS as ATRS
import Hoca.ATRS (aterm, AView (..))
import qualified Hoca.TreeGrammar as TG
import qualified Hoca.DFA as DFA
import qualified Hoca.FP as FP
import qualified Hoca.Utils (tracePretty)
import qualified Hoca.Narrowing as N
import qualified Hoca.Uncurry as UC
import           Hoca.PCF (Exp)
import qualified Hoca.PCF2Atrs as PCF2Atrs
import           Hoca.Problem (Symbol (..), Problem)
import qualified Hoca.Problem as Problem
import qualified Hoca.UsableRules as UR

import Hoca.Strategy
import Data.Maybe (catMaybes)
import Data.List (intersect)

-- Transformations

pcfToTrs :: Exp FP.Context :~> Problem Symbol Int
pcfToTrs = pure . PCF2Atrs.toProblem

reducibleVars :: (Ord f, Ord v) => Problem f v -> N.Narrowing (ATRS.ASym f) v v -> [v]
reducibleVars p n =
  [ v | v <- nub (T.vars (R.lhs rl))
      , any isCall (T.subterms ( mgu `apply` T.Var (Right v))) ]
      -- , null (UR.usableRules [mgu `apply` T.Var (Right v)] rules) ]
  where
    rl = N.narrowedWith n    
    mgu = N.narrowingMgu n
    isCall (aterm -> Var _)  = False
    isCall (aterm -> (_ :@ _)) = True
    isCall (aterm -> Fun f _) = f `elem` ds
    isCall _ = error "Hoca.Transform.normalisedVars match failure"
    ds = [ f | Fun f _ <- map aterm (RS.lhss (Problem.rules p)) ]
    
complexityReflecting :: (Ord f, Ord v) => Problem f v -> N.NarrowedRule (ATRS.ASym f) v v -> Bool
complexityReflecting p nr = all redexPreserving (N.narrowings nr) where
  redexPreserving n = varsMS (R.lhs rl) == varsMS (R.rhs rl) where
    rl = N.narrowedWith n
    varsMS = MS.fromList . filter (`elem` withCall) . T.vars
    withCall = reducibleVars p n

complexityPreserving :: (Ord f, Ord v) => Problem f v -> N.NarrowedRule (ATRS.ASym f) v v -> Bool
complexityPreserving p nr = all redexReflecting (N.narrowings nr) where
  redexReflecting n = varsMS (R.rhs rl) `MS.isSubsetOf` varsMS (R.lhs rl) where
    rl = N.narrowedWith n
    varsMS = MS.fromList . filter (`elem` withCall) . T.vars
    withCall = reducibleVars p n

narrow :: (Ord f, Ord v, Num v) => (Problem f v -> N.NarrowedRule (ATRS.ASym f) v v -> Bool) -> Problem f v :~> Problem f v
narrow sensible p = Problem.replaceRulesM narrowRule p where
  
  -- renameRule rl = R.rename f rl where
  --   f = either (\ v -> fromJust (lookup v lvs)) id
  --   lhs = R.lhs rl
  --   lvs = foldl insrt [(v,v) | Right v <- T.vars lhs] [v | Left v <- T.vars lhs]
  --   insrt vs v = (v, head (dropWhile (`elem` map snd vs) [v..])):vs

  renameRule = R.map (T.fold var T.Fun) where
     var (Left v) = T.Var (v * 2 + 1)
     var (Right v) = T.Var (v * 2)
  
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
  -- rules = Problem.rules p

-- narrow sensible = withInput $ \ p -> choice (map (Problem.replaceRulesM . applyNarrowing p) (narrowings p)) where
--   applyNarrowing p (i,n,nss) j _ ss
--     | i /= j = empty
--     | otherwise =
--         return [ (renameRule (N.narrowing ni) , ss ++ succs ni )
--                | ni <- N.narrowings n ] where
--           succs ni =
--             case lookup (N.narrowedWith ni) nss of
--              Nothing -> error "narrow rule id not found"
--              Just k -> Problem.cgSuccs p k
--   narrowings p =
--     [ (i,n,nss)
--     | (i,rl) <- rulesE
--     , let nss = [ (rl',j) | j <- Problem.cgSuccs p i, Just rl' <- [Problem.rule p j] ]
--     , n <- N.narrow rl (map fst nss)
--     , complexityReflecting p n
--     , sensible p n ]
--     where rulesE = Problem.rulesEnum p

--   renameRule = R.map (T.fold var T.Fun) where
--      var (Left v) = T.Var (v * 2 + 1)
--      var (Right v) = T.Var (v * 2)

-- [ (rl',j) | j <- Problem.cgSuccs p i, Just rl' <- [Problem.rule p j] ]
rewrite :: (Ord f, Ord v, Num v) => (Problem f v -> N.NarrowedRule (ATRS.ASym f) v v -> Bool) -> Problem f v :~> Problem f v
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
    case ATRS.headSymbol (R.lhs rl) of
     Just (l@Lambda {}) -> l `elem` createdFuns
     Just (l@Fix {}) -> l `elem` createdFuns
     _ -> True
  createdFuns = foldr ATRS.funsDL [] (RS.rhss (Problem.rules p))

dfaInstantiate :: (ATRS.TypedRule Symbol Int -> Int -> [ATRS.Term Symbol ()] -> Bool) -> Problem Symbol Int :~> Problem Symbol Int
dfaInstantiate refineP prob = 
  case ATRS.inferTypes rs of
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
         [ TG.Production DFA.startNonTerminal (TG.Terminal (ATRS.Sym f) [TG.NonTerminal (DFA.auxNonTerminal t) | t <- ATRS.inputTypes td])
         | (f, td) <- Map.toList sig, Problem.isMainSym f]
       constructorRules = 
         [ TG.Production (DFA.auxNonTerminal (ATRS.outputType td)) (TG.Terminal (ATRS.Sym c) [TG.NonTerminal (DFA.auxNonTerminal t) | t <- ATRS.inputTypes td])
         | (c, td) <- Map.toList sig, Problem.isConstructor c ]
           
     mkRefinements = DFA.refinements rs initialDFA

     argumentNormalised t = all norm (T.properSubterms t) where
       norm (T.Var _) = True
       norm (ATRS.atermM -> Just (_ ATRS.:@ _)) = False
       norm li = all (isNothing . unify li) (RS.lhss (map snd rs))

     T.Var {} `properInstOf` T.Fun {} = True
     (T.Fun _ ts) `properInstOf` (T.Fun _ ss) = or (zipWith properInstOf ts ss)
     _ `properInstOf` _ = False
       
  where rs = Problem.rulesEnum prob

uncurryRules :: Problem Symbol Int :~> Problem Symbol Int
uncurryRules p = Problem.fromRules <$> UC.uncurried (Problem.rules p)

etaSaturateRules :: Problem Symbol Int :~> Problem Symbol Int
etaSaturateRules p = Problem.fromRules <$> UC.etaSaturate (Problem.rules p)

compress :: Problem Symbol Int :~> Problem Symbol Int
compress p = Problem.replaceRulesM replace p where
  replace _ rl ss = Just [(R.map compressTerm rl,ss)]
  compressTerm (aterm -> Fun f ts) =
    case Map.lookup f cm of
     Just as -> ATRS.fun f (catMaybes (zipWith cti as ts))
     Nothing -> ATRS.fun f (map compressTerm ts)
  compressTerm (aterm -> t1 :@ t2) = compressTerm t1 `ATRS.app` compressTerm t2
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

-- todo check abort conditions
arglabel :: Problem Symbol Int :~> Problem Symbol Int
arglabel p
  | Map.null cl = empty
  | otherwise = Problem.replaceRulesM replace p
  where
    replace _ rl ss = Just [(R.map labelTerm rl,ss)]
    labelTerm (aterm -> Fun f ts) =
      case Map.lookup f cl of
       Just is -> ATRS.fun (withLabel [ts!!i | i <- is] f) (map labelTerm ts)
       Nothing -> ATRS.fun f (map labelTerm ts)
       where
         withLabel [] f = f
         withLabel (ti:ts') f =
           case aterm ti of
            Fun g _ -> Problem.Labeled (Problem.LSym g) (withLabel ts' f)
            _ -> error "Hoca.Transform.argLabel match failure"

    labelTerm (aterm -> t1 :@ t2) = labelTerm t1 `ATRS.app` labelTerm t2
    labelTerm t = t
  
    cl = foldl ins Map.empty (concatMap T.subterms (lhss ++ rhss)) where
      ins m (aterm -> Fun f ts) = Map.insertWith intersect f poss m where
            poss = [ i | (i,ti) <- zip [0..] ts, constructorRoot ti]
      ins m _ = m
    
      rs = Problem.rules p      
      lhss = RS.lhss rs
      rhss = RS.rhss rs
      constructorRoot (aterm -> Fun f _) = f `notElem` ds
      constructorRoot _ = False
      ds = [ f | Fun f _ <- map aterm lhss ]
