-- | 

module Hoca.Uncurry where

import Hoca.ATRS (Type(..), TypedRule)
import qualified Hoca.ATRS as ATRS
import qualified Hoca.Problem as Problem
import qualified Data.Rewriting.Term as T
import qualified Data.Rewriting.Rule as R
import Control.Applicative (Alternative, (<$>),(<*>), empty)

etaSaturateTyped :: [TypedRule f v] -> [TypedRule f (Either v Int)]
etaSaturateTyped = concatMap (etaSaturateRule 1 . ren) where
  etaSaturateRule i rl =
    case ATRS.getType (R.lhs rl) of
     tp1 :~> tp2 ->
       rl : etaSaturateRule (i + 1) (R.map saturate rl) where
         saturate t = T.Fun (ATRS.App, tp2) [t, T.Var (Right i,tp1)]
     _ -> [rl]
  ren = R.rename (\ (v,tp) -> (Left v,tp))

-- TODO check that head-variable free

uncurryRules :: (Monad m, Alternative m) => [TypedRule f v] -> m [ATRS.Rule (f,Int) v]
uncurryRules = mapM (uncurryRuleM . ATRS.unTypeRule) where
  uncurryRuleM rl = 
    R.Rule <$> uncurryTermM (R.lhs rl)
           <*> uncurryTermM (R.rhs rl)
  uncurryTermM (T.Var v) = return (T.Var v)
  uncurryTermM t =
    case ATRS.function t of
     Just (T.Fun (ATRS.Sym f) ts) ->
       ATRS.fun (f,length as) <$> mapM uncurryTermM (ts ++ as) where 
         as = ATRS.args t
     _ -> empty
     
uncurried :: (Monad m, Alternative m) => [ATRS.Rule Problem.Symbol Int] -> m [ATRS.Rule Problem.Symbol Int]
uncurried rs =
  case ATRS.inferTypes (zip [1..] rs) of
   Left _ -> empty
   Right (_, map (fst . snd) -> rs') -> 
     map ren <$> uncurryRules (etaSaturateTyped rs')
   where
     ren = R.map (T.fold var fun)
     var (Left v) = T.Var (v * 2 + 1)
     var (Right v) = T.Var (v * 2)
     fun (ATRS.Sym (f,i)) as = ATRS.fun (Problem.Labeled (Problem.LInt i) f) as
     fun _ _ = error "uncurried: TRS contains application symbol"
     
-- etaSaturate :: (Monad m, Alternative m) => [ATRS.Rule Problem.Symbol Int] -> m [ATRS.Rule Problem.Symbol Int]
etaSaturate :: (Monad m, Alternative m) => [ATRS.Rule Problem.Symbol Int] -> m [ATRS.Rule Problem.Symbol Int]
etaSaturate rs =
  case ATRS.inferTypes (zip [1..] rs) of
   Left _ -> empty
   Right (_, map (fst . snd) -> rs') -> return (map ren (ATRS.unTypeRules (etaSaturateTyped rs'))) where
     ren = R.map (T.fold var fun)
     var (Left v) = T.Var (v * 2 + 1)
     var (Right v) = T.Var (v * 2)
     fun f as = T.Fun f as
      
    
