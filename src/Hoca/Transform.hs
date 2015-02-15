-- | 

module Hoca.Transform (
  pcfToTrs
  -- * Simplifications
  , usableRules
  , uncurryRules
  , etaSaturateRules
  , dfaInstantiate
    -- ** Rule Narrowing
  , narrow
  , rewrite
  , complexityPreserving
  , complexityReflecting
)
       where

import           Control.Applicative (Applicative, Alternative, empty, pure, (<$>))
import qualified Data.Map as Map
import           Data.Maybe (listToMaybe, fromJust, isNothing, fromMaybe)
import qualified Data.MultiSet as MS
import qualified Data.Rewriting.Rule as R
import qualified Data.Rewriting.Rules as RS
import           Data.Rewriting.Substitution (unify, apply)
import qualified Data.Rewriting.Term as T
import qualified Hoca.ATRS as ATRS
import qualified Hoca.TreeGrammar as TG
import qualified Hoca.DFA as DFA
import qualified Hoca.FP as FP
import qualified Hoca.Narrowing as N
import qualified Hoca.Uncurry as UC
import           Hoca.PCF (Exp)
import qualified Hoca.PCF2Atrs as PCF2Atrs
import           Hoca.Problem (Symbol (..), Problem)
import qualified Hoca.Problem as Problem
import qualified Hoca.UsableRules as UR

-- Transformations

pcfToTrs :: Applicative m => Exp FP.Context -> m (Problem Symbol Int)
pcfToTrs = pure . PCF2Atrs.toProblem

normalisedVars :: (Ord f, Ord v) => Problem f v -> N.Narrowing (ATRS.ASym f) v v -> [v]
normalisedVars p n =
  [ v | v <- T.vars (R.lhs rl)
      , null (UR.usableRules [mgu `apply` T.Var (Right v)] rules) ]
  where
    rl = N.narrowedWith n    
    rules = Problem.rules p
    mgu = N.narrowingMgu n
    
complexityReflecting :: (Ord f, Ord v) => Problem f v -> N.NarrowedRule (ATRS.ASym f) v v -> Bool
complexityReflecting p nr = all redexPreserving (N.narrowings nr) where
  redexPreserving n = varsMS (R.lhs rl) `MS.isSubsetOf` varsMS (R.rhs rl) where
    rl = N.narrowedWith n
    varsMS = MS.fromList . filter (`notElem` normalised) . T.vars
    normalised = normalisedVars p n

complexityPreserving :: (Ord f, Ord v) => Problem f v -> N.NarrowedRule (ATRS.ASym f) v v -> Bool
complexityPreserving p nr = all redexReflecting (N.narrowings nr) where
  redexReflecting n = varsMS (R.rhs rl) `MS.isSubsetOf` varsMS (R.lhs rl) where
    rl = N.narrowedWith n
    varsMS = MS.fromList . filter (`notElem` normalised) . T.vars
    normalised = normalisedVars p n

narrow :: (Ord f, Ord v, Enum v, Alternative m, Monad m) => (Problem f v -> N.NarrowedRule (ATRS.ASym f) v v -> Bool) -> Problem f v -> m (Problem f v)
narrow sensible p = Problem.replaceRulesM narrowRule p where
  
  renameRule rl = R.rename f rl where
    f = either (\ v -> fromJust (lookup v lvs)) id
    lhs = R.lhs rl
    lvs = foldl insrt [(v,v) | Right v <- T.vars lhs] [v | Left v <- T.vars lhs]
    insrt vs v = (v, head (dropWhile (`elem` map snd vs) [v..])):vs
                 
  narrowRule _ rl ss = 
    case listToMaybe [ ni | ni <- N.narrow rl rules, complexityReflecting p ni, sensible p ni ] of
     Nothing -> empty
     Just ni -> return [(renameRule (N.narrowing n)
                         , ss ++ Problem.cgSuccs p nidx )
                       | n <- N.narrowings ni
                       , let nidx = fromMaybe (error "narrow rule id not found") (Problem.indexOf p (N.narrowedWith n))
                       ]
  rules = Problem.rules p

rewrite :: (Ord f, Ord v, Enum v, Alternative m, Monad m) => (Problem f v -> N.NarrowedRule (ATRS.ASym f) v v -> Bool) -> Problem f v -> m (Problem f v)
rewrite sensible = narrow sensible' where
  sensible' rs nr = all (\ nw -> R.lhs (N.narrowedRule nr) `T.isVariantOf` R.lhs (N.narrowing nw)) (N.narrowings nr)
                    && sensible rs nr
  
usableRules :: (Ord v, Alternative m) => Problem Symbol v -> m (Problem Symbol v)
usableRules p
  | Problem.size p' < Problem.size p = pure p'
  | otherwise = empty
  where
    p' = Problem.removeUnusedRules (Problem.withEdges edgeP p)
    rs = Problem.rules p
    r1 `edgeP` r2 = maybe False (elem r2) (lookup r1 ss)
    ss = [(r,UR.calls (R.rhs r) rs) | r <- rs ]

dfaInstantiate :: (Monad f, Alternative f) => (ATRS.TypedRule Symbol Int -> Int -> [ATRS.Term Symbol ()] -> Bool) -> Problem Symbol Int -> f (Problem Symbol Int)
dfaInstantiate refineP prob = 
  case ATRS.inferTypes rs of
   Left _ -> empty
   Right (sig,ers) -> Problem.replaceRulesM replace prob where
     replace i _ _ = pure [(rl,succs) | rl <- rs', argumentNormalised rl] where
       -- | null vs && all (`elem` succs) (Problem.calleeIdxs prob i) = empty
       -- | otherwise 
           (rs',succs) = mkRefinements i refineP'
           refineP' = maybe (const (const False)) (refineP . fst) (lookup i ers)
           
     initialDFA = TG.fromList (startRules ++ constructorRules) where
       startRules = 
         [ TG.Production DFA.startNonTerminal (TG.Terminal (ATRS.Sym f) [TG.NonTerminal (DFA.auxNonTerminal t) | t <- ATRS.inputTypes td])
         | (f, td) <- Map.toList sig, Problem.isMainSym f]
       constructorRules = 
         [ TG.Production (DFA.auxNonTerminal (ATRS.outputType td)) (TG.Terminal (ATRS.Sym c) [TG.NonTerminal (DFA.auxNonTerminal t) | t <- ATRS.inputTypes td])
         | (c, td) <- Map.toList sig, Problem.isConstructor c ]
           
     mkRefinements = DFA.refinements rs initialDFA

     argumentNormalised rl = all norm (T.properSubterms (R.lhs rl)) where
       norm (T.Var _) = True
       norm (ATRS.atermM -> Just (_ ATRS.:@ _)) = False
       norm li = all (isNothing . unify li) (RS.lhss (map snd rs))
  where rs = Problem.rulesEnum prob

uncurryRules :: (Monad m, Alternative m) => Problem Symbol Int -> m (Problem Symbol Int)
uncurryRules p = Problem.fromRules <$> UC.uncurried (Problem.rules p)

etaSaturateRules :: (Monad m, Alternative m) => Problem Symbol Int -> m (Problem Symbol Int)
etaSaturateRules p = Problem.fromRules <$> UC.etaSaturate (Problem.rules p)
