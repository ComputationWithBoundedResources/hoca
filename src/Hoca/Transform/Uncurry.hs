-- | Type directed uncurrying for head-variable free rewrite rules

module Hoca.Transform.Uncurry ( 
  etaSaturate
  , uncurried
  , TRSSymbol
  ) where

import Hoca.Problem
import Hoca.Data.MLTypes
import Data.Rewriting.Applicative.Term hiding (isInstanceOf)
import Data.Rewriting.Applicative.Rule hiding (vars)
import Data.Rewriting.Applicative.Rules (applicativeArity)
import qualified Data.Map as Map
import Control.Monad (forM)
import Control.Monad.State (evalStateT, put, get)
import Control.Monad.Writer (tell, runWriterT)
import Control.Applicative (empty)
import Hoca.Strategy 
import Hoca.Data.Symbol
import Data.Maybe (fromJust)

etaSaturate' :: Ord f => Problem f Int -> Maybe [(Int, [TRule f Int])]
etaSaturate' p =
  forM (rulesEnum p) $ \ (idx,trl) -> do 
    trls <- aaTerm (lhs (theRule trl)) >>= saturate trl
    return (idx,trls)
  where
    aa = applicativeArity (theRule `map` rules p)

    aaTerm (aformM -> Just (atermM -> Just (TFun f _),as)) = Just (aa f - length as)
    aaTerm _ = Nothing

    saturate trl n = evalStateT (saturateM trl n) (ftvs,fvs) where
      ftvs = [maximum (-1:tvsFromTRule trl) + 1..]
      fvs = [maximum (-1:vars (rhs (theRule trl))) + 1..]

    saturateM _ 0 = return []
    saturateM trl n = do 
      (tv1:tv2:ntvs, v:vs) <- get
      put (ntvs,vs)
      let 
        rl' = mapSides (`app` Var v) (theRule trl)
        trl' = case theType trl of 
                 tp1 :-> tp2 -> TRule { theRule = rl', theEnv = (v,tp1) : theEnv trl              , theType = tp2 }
                 TyVar tv    -> TRule { theRule = rl', theEnv = (v,TyVar tv1) : (s `o` theEnv trl), theType = TyVar tv2 } where
                                s = singletonSubst tv (TyVar tv1 :-> TyVar tv2)
                 _           -> error "Hoca.Transform.Uncurry: Rule not properly typed"
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


sym :: Symbol -> Int -> TRSSymbol
sym f = TRSSymbol (symbolToName f)

uncurried' :: Problem Symbol Int :=> Problem TRSSymbol Int 
uncurried' p = do 
  (trs,ds) <- runWriterT (uncurryRulesM `mapM` rules p) 
  return (fromRules (translateStartTerms ds) (signatureFromList ds) trs)
  where 
    translateStartTerms ds = 
        StartTerms { defs = fromDS defs, constrs = fromDS constrs } where
               fromDS sel = [ f | f@(TRSSymbol g _) ::: _ <- ds
                                , g `elem` (symbolToName `map` sel (startTerms p))]
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
             tell [ sym f n ::: tins :~> tret] >> return tret
          
        uc (atermM -> Just (TVar v)) = return (var v, fromJust (lookup v env))
        uc (aformM -> Just (atermM -> Just (TFun f ts), as)) = do
          (ss,_) <- unzip <$> uc `mapM` (ts ++ as)
          tp <- recordTypeDecl f (length as)
          return (fun (sym f (length as)) ss, tp)
        uc _ = empty
        
      (l,tp) <- uc (lhs rl)
      (r,_) <- uc (rhs rl)
      return (env |- (Rule l r, tp))
      

uncurried :: Problem Symbol Int :=> Problem TRSSymbol Int 
uncurried = try (exhaustive etaSaturate) >=> uncurried'

     
