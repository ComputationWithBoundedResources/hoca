-- | Type directed uncurrying for head-variable free rewrite rules

module Hoca.Uncurry ( uncurried ) where

import qualified Data.Rewriting.Applicative.SimpleTypes as ST
import Data.Rewriting.Applicative.SimpleTypes (Type (..))
import qualified Hoca.Problem as Problem

import qualified Data.Rewriting.Applicative.Term as T
import qualified Data.Rewriting.Applicative.Rule as R
import qualified Data.Rewriting.Rule as Rule

import Control.Monad (foldM)
import Control.Applicative (Alternative, (<$>),(<*>), empty)

etaSaturateTyped :: (Monad m, Alternative m) => [ST.ATypedRule f v] -> m [ST.ATypedRule f (Either v Int)]
etaSaturateTyped rs = foldM (etaSaturateRule 1) [] (map ren rs) where
  etaSaturateRule i rs' rl =
    case ST.getType (R.lhs rl) of
     tp1 :~> _ -> do
       let v = ST.var tp1 (Right i)
       rl' <- Rule.Rule <$> (R.lhs rl `ST.app` v) <*> (R.rhs rl `ST.app` v)
       etaSaturateRule (i+1) (rl:rs') rl'
     _ -> return (rl : rs' )
  ren = R.rename (\ (v,tp) -> (Left v,tp))

-- TODO check that head-variable free
uncurryRules :: (Monad m, Alternative m) => [ST.ATypedRule f v] -> m [R.ARule (f,Int) v]
uncurryRules = mapM (uncurryRuleM . ST.unTypeRule) where
  uncurryRuleM rl = 
    R.rule <$> uncurryTermM (R.lhs rl)
           <*> uncurryTermM (R.rhs rl)
  uncurryTermM (T.atermM -> Just (T.Var v)) = return (T.var v)
  uncurryTermM (T.aform -> Just (T.atermM -> Just (T.Fun f ts), as)) =
       T.fun (f,length as) <$> mapM uncurryTermM (ts ++ as)
  uncurryTermM _ = empty
     
uncurried :: (Monad m, Alternative m) => [R.ARule Problem.Symbol Int] -> m [R.ARule Problem.Symbol Int]
uncurried rs =
  case ST.inferTypes (zip [1..] rs) of
   Left _ -> empty
   Right (_, map (fst . snd) -> rs') -> 
     map ren <$> (etaSaturateTyped rs' >>= uncurryRules)
   where
     ren = R.mapRule (T.fold var fun)
     var (Left v) = T.var (v * 2 + 1)
     var (Right v) = T.var (v * 2)
     fun (T.Sym (f,i)) as = T.fun (Problem.Labeled i f) as
     fun _ _ = error "uncurried: TRS contains application symbol"
     
