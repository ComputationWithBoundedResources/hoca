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
import Debug.Trace (trace)

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




insertInto :: (t -> t -> Bool) -> [t] -> t -> [t]
insertInto _ [] b = [b]
insertInto isInstanceOf (a:as) b
  | a `isInstanceOf` b = insertInto isInstanceOf as b
  | b `isInstanceOf` a = a:as
  | otherwise = a : insertInto isInstanceOf as b

-- avoid redundant rules, i.e. those that are instances of other rules
newtype RS f v = RS [R.Rule f v]

instance (Eq f, Ord v) => Monoid (RS f v) where
  mempty = RS []
  mappend (RS rs1) (RS rs2) = RS (foldl (insertInto R.isInstanceOf) rs1 rs2)

rsFromList :: (Ord v, Eq f) => [R.Rule f v] -> RS f v 
rsFromList rs = RS (foldl (insertInto R.isInstanceOf) [] rs)

rsToList :: RS f v -> [R.Rule f v]
rsToList (RS l) = l

-- termset, implicitly closed under instances

newtype TS f v = TS [T.Term f v]

instance (Eq f, Ord v) => Monoid (TS f v) where
  mempty = TS []
  mappend (TS rs1) (TS rs2) = TS (foldl (insertInto T.isInstanceOf) rs1 rs2)

tsFromList :: (Ord v, Eq f) => [T.Term f v] -> TS f v 
tsFromList ts = TS (foldl (insertInto T.isInstanceOf) [] ts)

tsToList :: TS f v -> [T.Term f v]
tsToList (TS l) = l

-- ts1 `tsInsertInto` ts2 = foldl insert 

tracePretty :: PP.Pretty e => e -> a -> a
tracePretty e = trace (render (PP.pretty e) "")
  where render = PP.displayS . PP.renderSmart 1.0 80


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
      subst <- ST.fromMap <$>
               foldM (\ m v@(_,tp) -> Map.insert v <$> freshTVar tp <*> return m)
               Map.empty (R.vars rl)
      return (R.map (fromJust . S.gApply subst) rl) 

    abort = lift (lift (throwError ()))

    logStderr t rs =
      tracePretty (PP.pretty (unType t)
                   PP.<+> PP.text "::"
                   PP.<+> (PP.pretty (getType t))
                   PP.<$> PP.indent 2 (PP.text "~>"
                                       PP.<+> PP.semiBraces (map (PP.pretty . unType) (tsToList rs))
                                       PP.<> PP.line))
         (return ())

    record urs = lift (tell (rsFromList urs))

    visited t = do
      (nv,seen) <- lift get
      when (nv > numVisits) abort
      if any (T.isInstanceOf t) seen
        then lift (put (nv+1, seen)) >> return True
        else lift (put (nv+1, t : seen)) >> return False                 

    narrowedUsableRulesM rules = mapM_ evalM
      where
        prod :: [[a]] -> [[a]]
        prod [] = [[]]
        prod (as:ass) = [ ai:asi | ai <- as, asi <- prod ass ]

        recursive t = any (t `T.isInstanceOf`) [R.lhs r | r <- rules, r `elem` usableRules [R.rhs r] rules]

        ofBaseType t = case getType t of {BT{} -> True; _ -> False}

        tsFromTerm t = tsFromList [t]

        evalM (T.Var (_,tp)) = tsFromTerm <$> freshTVar tp
        evalM t@(T.Fun f ts) = do
          seen <- visited t
          if seen && (ofBaseType t || recursive t)
           then tsFromTerm <$> freshTVar (getType t)
           else do
             ss <- map (T.Fun f) <$> (prod . map tsToList) <$> mapM evalM ts
             foldM (\ us si -> (`mappend` us) <$> stepM si) (tsFromList []) ss
         
        stepM t = case mapMaybe step rules of
                   [] -> return (tsFromList [t])
                   urs -> do
                     record urs
                     -- logStderr (unTypeRules urs)
                     rs <- mconcat <$> mapM evalM (RS.rhss urs)
                     logStderr t rs
                     return rs
          where
            step rl = appMgu rl <$> unify t (R.lhs rl)
            appMgu rl mgu = R.map (S.apply mgu) rl
              

