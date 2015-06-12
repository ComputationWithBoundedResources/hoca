-- | Type directed uncurrying for head-variable free rewrite rules

module Hoca.Transform.Uncurry ( 
  etaSaturate
  , uncurried 
  ) where

import Hoca.Problem
import Hoca.Data.MLTypes
import Data.Rewriting.Applicative.Term hiding (isInstanceOf)
import Data.Rewriting.Applicative.Rule hiding (vars)
import qualified Data.Map as Map
import Control.Monad (forM)
import Control.Monad.State (evalStateT, put, get)
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

etaSaturate' :: Ord f => Problem f Int -> Maybe [(Int, [TRule f Int])]
etaSaturate' p =
  forM (rulesEnum p) $ \ (idx,trl) -> do 
    trls <- aaTerm (lhs (theRule trl)) >>= saturate trl
    return (idx,trls)
  where
    aa = applicativeArity p

    aaTerm (aform -> Just (atermM -> Just (TFun f _),as)) = Just (aa f - length as)
    aaTerm _ = Nothing

    saturate trl n = evalStateT (saturateM trl n) (ftvs,fvs) where
      ftvs = [maximum (-1:tvsFromTRule trl) + 1..]
      fvs = [maximum (-1:vars (rhs (theRule trl))) + 1..]

    saturateM _ 0 = return []
    saturateM trl n = do 
      (tv1:tv2:ntvs, v:vs) <- get
      put (ntvs,vs)
      let 
        rl' = mapRule (`app` Var v) (theRule trl)
        trl' = case theType trl of 
                 tp1 :-> tp2 -> TRule { theRule = rl', theEnv = (v,tp1) : theEnv trl              , theType = tp2 }
                 TyVar tv    -> TRule { theRule = rl', theEnv = (v,TyVar tv1) : (s `o` theEnv trl), theType = TyVar tv2 } where
                                s = singletonSubst tv (TyVar tv1 :-> TyVar tv2)
      (:) trl' <$> saturateM trl' (n - 1)

etaSaturate :: Ord f  => Problem f Int :=> Problem f Int
etaSaturate p = 
  case etaSaturate' p of 
   Nothing -> empty 
   Just rs -> removeInstances <$> replaceRulesIdx replace p
     where 
       prs = theRule `map` rules p
       replace idx trl ss 
           | null trls = Nothing
           | otherwise = Just [ (trl',ss) | trl' <- trl:trls ] 
           where 
             trls = [ trl' 
                    | trl' <- fromJust (lookup idx rs)
                    , not (any (theRule trl' `isInstanceOf`) prs) ]

        

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
        shiftDecl n (tins :~> (t1 :-> t2)) = shiftDecl (n - 1) ((tins ++ [t1]) :~> t2)
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
uncurried = try (exhaustive etaSaturate) >=> uncurried'

     
