module Hoca.Problem.Type (
  Problem (..)
  , StartTerms (..)
  , TRule (..)
  , RuleGraph 
  , TypingEnv
  -- * Export
 , toWST
 , prettyWST
) where

import           Data.IntMap (IntMap)
import qualified Data.IntMap as IMap
import           Data.IntSet (IntSet)
import qualified Data.IntSet as ISet
import qualified Data.Map as Map
import           Data.List (nub)
import           Control.Arrow (second)
import           Data.Maybe (listToMaybe, catMaybes)
import qualified Data.Rewriting.Applicative.Rule as R
import qualified Data.Rewriting.Applicative.Term as T
import qualified Data.Rewriting.Applicative.Rules as TRS
import qualified Data.Rewriting.Problem as P
import qualified Data.Rewriting.Rules as RS
import           Hoca.Data.MLTypes (Signature, Type, Substitutable (..))
import           Hoca.Utils (ppSeq)
import qualified Text.PrettyPrint.ANSI.Leijen as PP


type TypingEnv v = [(v, Type)]

data TRule f v = 
  TRule { theRule :: R.ARule f v
        , theEnv :: TypingEnv v
        , theType :: Type }

instance Substitutable (TypingEnv v) where
  o s = map (second (o s))
  

type RuleGraph f v = IntMap (TRule f v,IntSet)

data StartTerms f = 
    StartTerms { defs :: [f]
               , constrs :: [f]
               }

data Problem f v = 
  Problem { ruleGraph :: RuleGraph f v
          , startTerms :: StartTerms f
          , signature :: Signature f
          }

prettyTerm :: (PP.Pretty f, PP.Pretty v, Eq v) => Bool -> (PP.Doc -> PP.Doc) -> TypingEnv v -> T.ATerm f v -> PP.Doc
prettyTerm True _ env (T.atermM -> Just (T.TVar v)) = 
  PP.text "x" PP.<> PP.pretty v
  PP.<> PP.text ":" PP.<> maybe (PP.text "?a") PP.pretty (lookup v env)
prettyTerm False _ _ (T.atermM -> Just (T.TVar v)) = 
  PP.text "x" PP.<> PP.pretty v
prettyTerm st _ env (T.atermM -> Just (T.TFun f ts)) = 
  PP.pretty f PP.<> PP.parens (ppSeq (PP.text ", ") [ prettyTerm st id env ti | ti <- ts])
prettyTerm st par env (T.atermM -> Just (t1 T.:@ t2)) = 
  par (prettyTerm st id env t1 PP.</> prettyTerm st PP.parens env t2) where
prettyTerm _ _ _ _ = PP.text "NON-WELL-FORMED-TERM"    
  

instance (Eq f, PP.Pretty f) => PP.Pretty (Problem f Int) where
  pretty p =
    PP.vcat
    [ PP.int i 
      PP.<> PP.text ":" 
      PP.<+> PP.hang 2 (prettyTerm False id env (R.lhs rl)
                        PP.<+> PP.text "-->" 
                        PP.</> PP.align (prettyTerm False id env (R.rhs rl)
                                         PP.<+> PP.text ":"
                                         PP.<+> PP.pretty (theType trl)))
    | (i,trl) <- rs
    , let rl = theRule trl
    , let env = theEnv trl ]
    PP.<$> PP.text ""
    PP.<$> PP.text "where"
    PP.<$> PP.indent 2 (PP.align (PP.pretty sig))
      where 
        syms = TRS.funs (map (theRule . snd) rs)
        sig = Map.filterWithKey (\ k _ -> k `elem` syms) (signature p) 
        rs = [(i,trl) | (i,(trl,_)) <- IMap.toList (ruleGraph p)]
      
    -- where
    --   ppVar i = PP.text "x" PP.<> PP.int i

      

toWST :: (PP.Pretty f, Eq f, Eq v) => Problem f v -> P.Problem (T.ASym f) v
toWST p = P.Problem {
  P.startTerms = P.AllTerms
  , P.strategy = P.Innermost
  , P.theory = Nothing
  , P.rules = P.RulesPair { P.strictRules = trs, P.weakRules = [] }
  , P.variables = nub (RS.vars trs)
  , P.symbols = nub (RS.funs trs)
  , P.comment = Nothing }
  where
    trs = map (theRule . fst) (IMap.elems (ruleGraph p))

prettyWST :: (PP.Pretty f, Eq f) => Problem f Int -> PP.Doc
prettyWST = P.prettyWST PP.pretty ppVar . toWST where
  ppVar i = PP.text "x" PP.<> PP.int i



