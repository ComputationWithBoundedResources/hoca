-- | 

module Hoca.Transform (
  -- * Combinators
  try
  , (>=>)
  , repeated
  , exhaustive
  , modifyRules
  , traceProblem
  -- * Transformations
  , pcfToTrs
  , narrow
  , rewrite
  , neededRules
  , usableRules
  , dfaInstantiate
  -- * Re-exported Datatypes
  , Symbol (..)
  , Var
  , Rule
  , Problem
  , Type (..)
)
       where

import           Control.Applicative ((<$>), Applicative, Alternative, empty, pure)
import           Control.Monad.RWS
import           Data.Either (partitionEithers)
import           Data.List (nub)
import qualified Data.Map as Map
import           Data.Maybe (listToMaybe, fromJust, isNothing)
import qualified Data.MultiSet as MS
import qualified Data.Rewriting.Problem as P
import qualified Data.Rewriting.Rule as R
import qualified Data.Rewriting.Rules as RS
import           Data.Rewriting.Substitution (unify)
import qualified Data.Rewriting.Term as T
import           Hoca.ATRS
import qualified Hoca.DFA as DFA
import qualified Hoca.FP as FP
import qualified Hoca.Narrowing as N
import           Hoca.PCF (Strategy(..), Exp)
import           Hoca.PCF2Atrs (Symbol (..), Problem, Var, toProblem, prettyProblem)
import qualified Hoca.UsableRules as UR
import           Hoca.Utils (rsFromList, rsToList, tracePretty)
import qualified Text.PrettyPrint.ANSI.Leijen as PP


-- combinators
try :: (Strategy m) => (a -> m a) -> a -> m a
try m a = m a <||> return a

repeated :: (Strategy m) => Int -> (a -> m a) -> a -> m a
repeated n m
  | n <= 0 = return
  | otherwise = try (m >=> repeated (n-1) m)

exhaustive :: Strategy m => (a -> m a) -> a -> m a
exhaustive rel = try (rel >=> exhaustive rel) 


modifyRules :: Applicative m => ([Rule Symbol Var] -> m [Rule Symbol Var]) -> Problem -> m Problem
modifyRules m prob = f <$> m strict
  where
    f rs = prob { P.rules = P.RulesPair { P.strictRules = rs', P.weakRules = []}
               , P.variables = nub (RS.vars rs')
               , P.symbols = nub (RS.funs rs') }
      where rs' = rsToList (rsFromList rs)
    rp = P.rules prob
    strict = P.strictRules rp

traceProblem :: Applicative m => String -> Problem -> m Problem
traceProblem s prob = tracePretty doc (pure prob) where
  ln c = PP.text (replicate 80 c)
  doc =
    PP.text s
    PP.<$> ln '-'
    PP.<$> PP.indent 2 (prettyProblem prob)
    PP.<$> ln '='
    PP.<$> PP.text ""


-- Transformations

pcfToTrs :: Applicative m => Exp FP.Context -> m Problem
pcfToTrs = pure . toProblem

narrow :: Alternative m => ([Rule Symbol Var] -> N.NarrowedRule (ASym Symbol) (Either Var Var) -> Bool) -> Problem -> m Problem
narrow sensible = modifyRules narrowRules where
  narrowRules rules =
    case partitionEithers (map narrowRule rules) of
     (_,[]) -> empty
     (untransformed,transformed) -> pure (untransformed ++ concat transformed)
    where
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
      
      narrowRule rl = 
        case listToMaybe [ ni | ni <- N.narrow rl rules, sound ni, sensible rules ni ] of
         Nothing -> Left rl
         Just ni -> Right [renameRule (N.narrowing n) | n <- N.narrowings ni]


rewrite :: Alternative m => ([Rule Symbol Var] -> N.NarrowedRule (ASym Symbol) (Either Var Var) -> Bool) -> Problem -> m Problem
rewrite sensible = narrow sensible' where
  sensible' rs nr = all (\ nw -> R.lhs (N.narrowedRule nr) `T.isVariantOf` R.lhs (N.narrowing nw)) (N.narrowings nr)
                    && sensible rs nr
  
usableRules :: (Alternative m) => Problem -> m Problem
usableRules = modifyRules (\ rs -> pure (UR.usableRules [ t | t@(T.Fun (Sym Main) _) <- RS.lhss rs] rs))

neededRules :: (Alternative m) => Problem -> m Problem
neededRules = modifyRules nr
  where
    nr rs = pure (filter needed rs) where 
        needed rl =
          case headSymbol (R.lhs rl) of
           Just (l@Lambda {}) -> l `elem` createdFuns
           Just (l@Fix {}) -> l `elem` createdFuns           
           _ -> True
        createdFuns = foldr funsDL [] (RS.rhss rs)

dfaInstantiate :: Alternative m => (TypedRule Symbol Var -> [Var]) -> Problem -> m Problem
dfaInstantiate abstractVars = modifyRules instantiateRules where
  instantiateRules rs =
    case inferTypes rs of
     Left _ -> empty
     Right (sig, ers) -> pure (concatMap refinements ers) where     
         initialDFA = DFA.fromRules (startRules ++ constructorRules)
         startRules = 
           [ DFA.Rule DFA.startSymbol (DFA.fun (Sym Main) [DFA.terminal (DFA.auxSymbol t) | t <- inputTypes td])
           | (Main, td) <- Map.toList sig]
         constructorRules = 
           [ DFA.Rule (DFA.auxSymbol (outputType td)) (DFA.fun (Sym c) [DFA.terminal (DFA.auxSymbol t) | t <- inputTypes td])
           | (c@Con{}, td) <- Map.toList sig ]
           
         mkRefinements = DFA.refinements rs initialDFA

         refinements (trl,_) = filter argumentNormalised (mkRefinements rl (`elem` abstractedVars)) where
           rl = unTypeRule trl
           abstractedVars = nub (abstractVars trl)
      
         argumentNormalised rl = all norm (T.properSubterms (R.lhs rl)) where
           norm (T.Var _) = True
           norm (atermM -> Just (_ :@ _)) = False
           norm li = all (isNothing . unify li) (RS.lhss rs)
