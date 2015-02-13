-- | 

module Hoca.Transform (
  -- * Combinators
  try
  , (>=>)
  , (<=>)
  , repeated
  , exhaustive
  , traced
  -- * Transformations
  , pcfToTrs
  , narrow
  , rewrite
  , neededRules
  , usableRules
  , uncurryRules
  , etaSaturateRules
  , dfaInstantiate
)
       where

import           Control.Applicative (Applicative, Alternative, empty, pure)
import           Control.Monad.RWS
import qualified Data.Map as Map
import           Data.Maybe (listToMaybe, fromJust, isNothing)
import qualified Data.MultiSet as MS
import qualified Data.Rewriting.Rule as R
import qualified Data.Rewriting.Rules as RS
import           Data.Rewriting.Substitution (unify)
import qualified Data.Rewriting.Term as T
import qualified Hoca.ATRS as ATRS
import qualified Hoca.TreeGrammar as TG
import qualified Hoca.DFA as DFA
import qualified Hoca.FP as FP
import qualified Hoca.Narrowing as N
import Hoca.Strategy
import qualified Hoca.Uncurry as UC
import           Hoca.PCF (Exp)
import qualified Hoca.PCF2Atrs as PCF2Atrs
import           Hoca.Problem (Symbol (..), Problem)
import qualified Hoca.Problem as Problem
import qualified Hoca.UsableRules as UR
import           Hoca.Utils (tracePretty)
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Data.Maybe (fromMaybe)
import Control.Applicative ((<$>))


-- Transformations

pcfToTrs :: Applicative m => Exp FP.Context -> m (Problem Symbol Int)
pcfToTrs = pure . PCF2Atrs.toProblem

narrow :: (Ord f, Ord v, Enum v, Alternative m, Monad m) => (Problem f v -> N.NarrowedRule (ATRS.ASym f) v v -> Bool) -> Problem f v -> m (Problem f v)
narrow sensible p = Problem.replaceRulesM narrowRule p where
  sound nr =
    all (redexPreserving . N.narrowedWith) (N.narrowings nr)
    || argumentNormalised (N.narrowSubterm nr)
         
  redexPreserving rl = varsMS (R.lhs rl) `MS.isSubsetOf` varsMS (R.rhs rl) where
    varsMS = MS.fromList . T.vars
           
  argumentNormalised (T.Fun _ ts) = null (UR.usableRules ts rules)
  argumentNormalised _ = True
        
  renameRule rl = R.rename f rl where
    f = either (\ v -> fromJust (lookup v lvs)) id
    lhs = R.lhs rl
    lvs = foldl insrt [(v,v) | Right v <- T.vars lhs] [v | Left v <- T.vars lhs]
    insrt vs v = (v, head (dropWhile (`elem` map snd vs) [v..])):vs
                 
  narrowRule _ rl ss = 
    case listToMaybe [ ni | ni <- N.narrow rl rules, sound ni, sensible p ni ] of
     Nothing -> empty
     Just ni -> return [(renameRule (N.narrowing n)
                         , ss ++ Problem.calleeIdxs p nidx )
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

neededRules :: (Monad m, Alternative m, Ord v) => Problem Symbol v -> m (Problem Symbol v)
neededRules p = Problem.replaceRulesM (\ _ rl _ -> if needed rl then empty else pure []) p where
  needed rl =
    case ATRS.headSymbol (R.lhs rl) of
     Just (l@Lambda {}) -> l `elem` createdFuns
     Just (l@Fix {}) -> l `elem` createdFuns           
     _ -> True
  createdFuns = foldr ATRS.funsDL [] (RS.rhss (Problem.rules p))

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
