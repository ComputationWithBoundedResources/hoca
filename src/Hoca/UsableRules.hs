{-# LANGUAGE ScopedTypeVariables #-}
-- | 

module Hoca.UsableRules (
  usableRules
  , narrowedUsableRules
  ) where

import qualified Data.Rewriting.Rule as R
import qualified Data.Rewriting.Rules as RS
import qualified Data.Rewriting.Term as T
import qualified Data.Rewriting.Substitution as S
import qualified Data.Rewriting.Substitution.Type as ST
import           Data.List (partition)
import qualified Data.Map as Map
import Control.Monad.RWS
import Control.Monad.Error
import qualified Control.Monad.State.Lazy as State
import Control.Applicative ((<$>), (<*>), Applicative(..))
import Data.Rewriting.Substitution.Unify (unify)
import Data.Maybe (isJust, mapMaybe, fromJust)
import  Hoca.ATRS
import qualified Text.PrettyPrint.ANSI.Leijen as PP
-- import Debug.Trace (trace)

fresh :: MonadState Int m => m Int
fresh = State.modify succ >> get

runVarSupplyT :: Monad m => State.StateT Int m a -> m a
runVarSupplyT = flip State.evalStateT 0

runVarSupply :: State.State Int a -> a
runVarSupply = flip State.evalState 0

-- assumes that variables are disjoint
isUnifiableWith :: (Ord v1, Ord v2, Eq f) => T.Term f v1 -> T.Term f v2 -> Bool
isUnifiableWith t1 t2 = isJust (unify (T.rename Left t1) (T.rename Right t2))

-- cap f(t1,...,tn) == f(tcap(t1),...,tcap(tn))
cap :: (Eq f, Ord v1, Ord v2) => [R.Rule f v1] -> T.Term f v2 -> T.Term f Int
cap rs t = runVarSupply (capM t)
  where
    freshVar = T.Var <$> fresh
    lhss = RS.lhss rs

    capM (T.Var _) = freshVar
    capM (T.Fun f ts) = T.Fun f <$> mapM tcapM ts
    
    tcapM (T.Var _) = freshVar
    tcapM (T.Fun f ts) = do 
      s <- T.Fun f <$> mapM tcapM ts
      if any (isUnifiableWith s) lhss then freshVar else return s

usableRules :: (Eq f, Ord v1, Ord v2) => [T.Term f v1] -> [R.Rule f v2] -> [R.Rule f v2]
usableRules ts rules = walk (caps ts) [] rules
  where
    walk []     ur _  = ur
    walk (s:ss) ur rs = walk (caps (RS.rhss ur') ++ ss) (ur' ++ ur) rs'
      where
        (ur',rs') = partition (\ rl -> s `isUnifiableWith` R.lhs rl) rs
    caps ss = [ cap rules s | si <- ss, s@T.Fun{} <- T.subterms si ]    


-- rulesets -- avoid redundant rules, i.e. those that are instances of other rules
newtype RS f v = RS [R.Rule f v]

rsInsertInto :: (Ord v, Eq f) => [R.Rule f v] -> [R.Rule f v] -> [R.Rule f v]
rs1 `rsInsertInto` rs2 = foldl insert rs2 rs1
  where
    insert [] rl2 = [rl2]
    insert (rl1:rs) rl2
      | rl1 `R.isInstanceOf` rl2 = insert rs rl2
      | rl2 `R.isInstanceOf` rl1 = rl1:rs
      | otherwise = rl1 : insert rs rl2

instance (Eq f, Ord v) => Monoid (RS f v) where
  mempty = RS []
  mappend (RS rs1) (RS rs2) = RS (rs1 `rsInsertInto` rs2)

rsFromList :: (Ord v, Eq f) => [R.Rule f v] -> RS f v 
rsFromList rs = RS (rs `rsInsertInto` [])

rsToList :: RS f v -> [R.Rule f v]
rsToList (RS l) = l

-- tracePretty :: PP.Pretty e => e -> a -> a
-- tracePretty e a = trace (render (PP.pretty e) "") a
--   where render = PP.displayS . PP.renderSmart 1.0 80


narrowedUsableRules :: (PP.Pretty f, Ord v1, Eq f) => Int -> [TypedTerm f v] -> [TypedRule f v1] -> Maybe [TypedRule f Int]
narrowedUsableRules numVisits tts trules = maybeFromErr (rsToList . snd <$> evalRWST (runVarSupplyT runM) () (0,[]))
  where
    maybeFromErr = either (const Nothing) Just

    runM = do
      rts <- mapM renameTermM tts
      rrules <- mapM renameRuleM trules
      narrowedUsableRulesM rrules rts 

    freshTVar tp = do {v <- fresh; return (T.Var (v,tp)) }

    renameTermM (T.Var (_,tp)) = freshTVar tp
    renameTermM (T.Fun f ts) = T.Fun f <$> mapM renameTermM ts

    renameRuleM rl = do
      subst <- ST.fromMap <$> foldM (\ m v@(_,tp) -> Map.insert v <$> freshTVar tp <*> return m)
                               Map.empty (R.vars rl)
      return (R.map (fromJust . S.gApply subst) rl) 


    narrowedUsableRulesM rules = mapM_ evalM
      where
        prod :: [[a]] -> [[a]]
        prod [] = [[]]
        prod (as:ass) = [ ai:asi | ai <- as, asi <- prod ass ]
        
        abort = lift (lift (throwError ()))

        visited t = do
          (nv,seen) <- lift get
          when (nv > numVisits) abort
          if any (T.isInstanceOf t) seen
            then lift (put (nv+1, seen)) >> return True
            else lift (put (nv+1, t : seen)) >> return False                 
        
        evalM (T.Var (_,tp)) = (: []) <$> freshTVar tp
        evalM t@(T.Fun f ts) = do
          seen <- visited t
          case getType t of
           tp@(BT {}) | seen -> (: []) <$> freshTVar tp
           _ -> do
             ss <- map (T.Fun f) <$> prod <$> mapM evalM ts
             foldM (\ us si -> (++ us) <$> stepM si) [] ss
         
        stepM t = case mapMaybe step rules of
                   [] -> return [t]
                   urs -> do
                     lift (tell (rsFromList urs))
                     -- tracePretty (unTypeRules urs) (return ())
                     concat <$> mapM evalM (RS.rhss urs)
          where
            step rl = appMgu rl <$> unify t (R.lhs rl)
            appMgu rl mgu = R.map (S.apply mgu) rl
              

