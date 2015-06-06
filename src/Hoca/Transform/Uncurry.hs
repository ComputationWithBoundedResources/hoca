-- | Type directed uncurrying for head-variable free rewrite rules

module Hoca.Transform.Uncurry ( 
  etaSaturate
  , uncurried 
  ) where

import Hoca.Problem
import Hoca.Data.MLTypes
import Prelude hiding (try)
import Data.Rewriting.Applicative.Term
import Data.Rewriting.Applicative.Rule
import qualified Data.Map as Map
import Control.Monad (forM)
import Control.Monad.Writer (tell, runWriterT)
import Control.Applicative (empty)
import Hoca.Strategy 
import Hoca.Transform.Defunctionalize (Symbol (..))
import Data.Maybe (fromJust)

applicativeArity :: Ord f => Problem f v -> f -> Int
applicativeArity prob = \ f -> Map.findWithDefault 0 f m
  where
    m = Map.fromListWith max (aa [] terms)
   
    aa l [] = l
    aa l ((aterm -> TVar _ ):ts) = aa l ts    
    aa l ((aterm -> (TFun _ ts')):ts) = aa l (ts'++ts)
    aa l ((aform -> Just (atermM -> Just (TFun f thd),tas)):ts) = 
      aa ((f,length tas) : l) (thd ++ tas ++ ts)
    aa l ((aform -> Just (_,tas)):ts) = aa l (tas ++ ts)
    aa l (_:ts) = aa l ts
    terms = leftHandSides prob ++ rightHandSides prob

etaSaturate :: Ord f  => Problem f Int :=> Problem f Int
etaSaturate p = 
  case etaSaturate' p of 
   Nothing -> empty 
   Just rs -> replaceRulesIdx replace p 
     where 
       replace idx _ ss = case trls of {_:_:_ -> Just [ (trl,ss) | trl <- trls ]; _ -> Nothing }
         where trls = fromJust (lookup idx rs)

etaSaturate' :: Ord f => Problem f Int -> Maybe [(Int, [TRule f Int])]
etaSaturate' p =
  forM (rulesEnum p) $ \ (idx,trl) -> do 
    n <- aaTerm (lhs (theRule trl))
    trls <- saturate (ren trl) n
    return (idx,trls)
  where
    aa = applicativeArity p

    aaTerm (aform -> Just (atermM -> Just (TFun f _),as)) = Just (aa f - length as)
    aaTerm _ = Nothing

    ren = renameTRule (2 *)      
      
    saturate trl = saturate' [maximum (-1:tvsFromTRule trl) + 1..] trl
      
    saturate' _ trl 0 = return [trl]
    saturate' (tv1:tv2:ntvs) trl n = 
      case theType trl of 
       tp1 :-> tp2 -> 
         (:) trl <$> saturate' (tv1:tv2:ntvs) trl' (n - 1) where
           trl' = TRule { theRule = rl' , theEnv = (v,tp1) : theEnv trl , theType = tp2 }
           
       TyVar tv -> 
         (:) trl <$> saturate' ntvs trl' (n - 1) where
           s tv' = if tv == tv' then TyVar tv1 :-> TyVar tv2 else TyVar tv'
           trl' = TRule { theRule = rl' , theEnv = (v,TyVar tv1) : (s `o` theEnv trl) , theType = TyVar tv2 }
             
       _ -> Nothing
      where 
        v =  n * 2 + 1
        rl' = mapRule (`app` Var v) (theRule trl)

uncurried' :: Problem Symbol Int :=> Problem Symbol Int 
uncurried' p = do 
  (trs,ds) <- runWriterT (uncurryRulesM `mapM` rules p) 
  return (fromRules [f | f@(Labeled _ g) ::: _ <- ds, g `elem` mains p] (signatureFromList ds) trs)
  where 
    uncurryRulesM trl = do 
      let 
        rl = theRule trl
        env = theEnv trl

        shiftDecl 0 td = Just td
        shiftDecl n (tins :~> (t1 :-> t2)) = 
          shiftDecl (n - 1) ((tins ++ [t1]) :~> t2)
        shiftDecl _ _ = Nothing
        
        recordTypeDecl f n = 
          case Map.lookup f (signature p) >>= shiftDecl n of 
           Nothing -> empty
           Just (tins :~> tret) -> 
             tell [ Labeled n f ::: tins :~> tret] >> return tret
          
        uc (atermM -> Just (TVar v)) = return (var v, fromJust (lookup v env))
        uc (aform -> Just (atermM -> Just (TFun f ts), as)) = do
          (ss,_) <- unzip <$> uc `mapM` (ts ++ as)
          tp <- recordTypeDecl f (length as)
          return (fun (Labeled (length as) f) ss, tp)
        uc _ = empty
        
      (l,tp) <- uc (lhs rl)
      (r,_) <- uc (rhs rl)
      return (env |- (Rule l r, tp))
      

uncurried :: Problem Symbol Int :=> Problem Symbol Int 
uncurried = uncurried'

     
