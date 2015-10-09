-- | call by value PCF core over free algebra
module Hoca.PCF.Core
  ( Exp (..)
  , Symbol (..)
  , Program (..)
  , TypedExp
  , TypedProgram
    -- * constructors
  , symbol
    -- * operations
  , constructors
  , label
  , match
  , isInstanceOf
  , subExpressions
  , applySubst
    -- * reduction
  , beta
  , cond
  , apply
  , applyL
  , fixCBV
  , nf
  , cbv
  , ctxtClosure
  -- * Types
  , typeOf
  ) where

import           Hoca.Strategy
import           Hoca.PCF.Core.Types
import           Hoca.Utils (composeM)

import           Control.Applicative (Alternative(..))
import qualified Data.Set as Set
import qualified Data.IntMap as IntMap
import           Data.Maybe (isJust)
import           Control.Monad (foldM,guard)
import           Data.Function (on)
import           Data.List (sortBy)


constructors :: Exp l -> Set.Set Symbol
constructors (Con _ g _) = Set.singleton g
constructors (Abs _ _ e) = constructors e
constructors (App _ e1 e2) = constructors e2 `Set.union` constructors e1
constructors (Cond _ e cs) = foldl f (constructors e) cs
  where f fs (g,ei) = Set.insert g (constructors ei `Set.union` fs)
constructors (Fix _ _ es) = Set.unions (map constructors es)
constructors _ = Set.empty

subExpressions :: Exp l -> [Exp l]
subExpressions e@(Con _ _ ts) = e : concatMap subExpressions ts
subExpressions e@(Abs _ _ e1) = e : subExpressions e1
subExpressions e@(App _ e1 e2) = e : subExpressions e1 ++ subExpressions e2
subExpressions e@(Cond _ e1 cs) = e : subExpressions e1 ++ concatMap (subExpressions . snd) cs
subExpressions e@(Fix _ _ es) = e : concatMap subExpressions es 
subExpressions e = [e]

match :: Eq l2 => Exp l1 -> Exp l2 -> Maybe (Subst l2)
match e f = go 0 e f IntMap.empty where
  go k (Var _ i) t sub
    | i >= k = -- free variable
        let t' = shift' (-k) (-k) t
        in case IntMap.lookup (i-k) sub of
            Nothing | nonVarCapture k t -> Just (IntMap.insert (i-k) t' sub)
            Just s | s == t' -> Just sub
            _ -> Nothing
    | otherwise =
        case t of
         Var _ j | i == j -> Just sub
         _ -> Nothing
  go k (Con _ g1 ss) (Con _ g2 ts) sub
    | g1 /= g2 || length ss /= length ts = Nothing
    | otherwise = composeM (zipWith (go k) ss ts) sub
  go _ (Bot _) (Bot _) sub = Just sub
  go k (App _ s1 s2) (App _ t1 t2) sub =
   go k s1 t1 sub >>= go k s2 t2
  go k (Cond _ s cs) (Cond _ t ct) sub = do
    let
      srt = sortBy (compare `on` fst)
      (cs',ct') = (srt cs, srt ct)
    guard (map fst cs' == map fst ct')    
    go k s t sub >>= composeM (zipWith (go k) (map snd cs') (map snd ct'))
  go k (Fix _ i ss) (Fix _ j ts) sub = do
    guard (i == j)
    composeM (zipWith (go k) ss ts) sub
  go k (Abs _ _ s) (Abs _ _ t) sub = go (k+1) s t sub
  go _ _ _ _ = Nothing
  
  nonVarCapture k (Var _ v) = v >= k
  nonVarCapture k (Abs _ _ s) = nonVarCapture (k+1) s
  nonVarCapture k (Con _ _ ss) = all (nonVarCapture k) ss
  nonVarCapture k (App _ s1 s2) = nonVarCapture k s1 && nonVarCapture k s2
  nonVarCapture _ (Bot _) = True
  nonVarCapture k (Cond _ s cs) = nonVarCapture k s && all (nonVarCapture k . snd) cs
  nonVarCapture k (Fix _ _ ss) = all (nonVarCapture k) ss

applySubst :: Exp l -> Subst l -> Exp l
applySubst = IntMap.foldWithKey subst

isInstanceOf :: (Show l, Eq l) => Exp l -> Exp l -> Bool
isInstanceOf e f = isJust (match f e)

-- * substitution 
shift :: Int -> Exp l -> Exp l
shift = shift' 0

shift' :: Variable -> Variable -> Exp l -> Exp l
shift' c d v@(Var l k)
  | k < c = v
  | otherwise = Var l (k + d)
shift' c d (Con l f as) = Con l f (map (shift' c d) as)
shift' _ _ e@(Bot _) = e
shift' c d (Abs lv la e) = Abs lv la (shift' (c+1) d e)
shift' c d (App l e1 e2) = App l (shift' c d e1) (shift' c d e2)
shift' c d (Cond l e cs) = Cond l (shift' c d e) [(g, shift' c d e') | (g,e') <- cs]
shift' c d (Fix i l es) = Fix i l [shift' c d e | e <- es]
      
-- | @subst j e1 e2 == e2[j <- e1]@
subst :: Int -> Exp l -> Exp l -> Exp l
subst j e (Var l k)
  | k == j = e
  | otherwise = Var l k
subst j e (Con l f as) = Con l f (map (subst j e) as)
subst _ _ f@(Bot _) = f
subst j e (Abs lv le f) = Abs lv le (subst (j+1) (shift 1 e) f)
subst j e (App l f1 f2) = App l (subst j e f1) (subst j e f2)
subst j e (Cond l f cs) = Cond l (subst j e f) [(g, subst j e e') | (g,e') <- cs]
subst j e (Fix i l es) = Fix i l [subst j e ei | ei <- es]

-- * steps

apply :: Alternative m => Exp l -> Exp l -> m (Exp l)
apply (Abs  _ _ e) f = pure (shift (-1) (subst 0 (shift 1 f) e))
apply _ _ = empty

applyL :: (Alternative m, Monad m) => Exp l -> [Exp l] -> m (Exp l)
applyL = foldM apply

beta :: (Alternative m, Monad m) => Exp l -> m (Exp l)
beta (App _ e f) = e `apply` f
beta _ = empty

-- cond g(e1,...,en) [... (g,\a1...an.e) ...] -> e{e1/a1,...,en/an}
cond :: (Alternative m, Monad m) => Exp l -> m (Exp l)
cond (Cond _ (Con _ g es) cs) =
  case lookup g cs of
   Nothing -> empty
   Just eg -> foldM apply eg es
cond _ = empty


-- fix(\e.f) --> f{(\z.fix(\e.f) z) / e}
fixCBV :: (Alternative m, Monad m) => Exp l -> m (Exp l)
fixCBV (App l (Fix l' i fs) a)
  | 0 <= i && i < length fs =
      App l <$> (fs!! i) `applyL` [Fix l' j fs | j <- [0..length fs - 1]] <*> return a
fixCBV _ = empty

-- * combinators 
leftToRight :: (Alternative m, Monad m, Choice m) => (Exp l -> m (Exp l)) -> [Exp l] -> m [Exp l]
leftToRight _ [] = empty
leftToRight stp (f:fs) = reduceF <||> reduceFS
      where
        reduceF = (: fs) <$> stp f
        reduceFS = (:) f <$> leftToRight stp fs

oneOf :: (Alternative m, Monad m) => (Exp l -> m (Exp l)) -> [Exp l] -> m [Exp l]
oneOf _ [] = empty
oneOf stp (f:fs) = reduceF <|> reduceFS
      where
        reduceF = (: fs) <$> stp f
        reduceFS = (:) f <$> oneOf stp fs

ctxtClosure :: (Alternative m, Monad m) => (Exp l -> m (Exp l)) -> Exp l -> m (Exp l)
ctxtClosure stp e = ctxt e <|> stp e
  where
    ctxt (App l e1 e2) = do
      [f1,f2] <- oneOf (ctxtClosure stp) [e1,e2]
      return (App l f1 f2)
    ctxt (Con l g es) = Con l g <$> oneOf (ctxtClosure stp) es
    ctxt (Cond l f cs) = redF <|> redCS
      where
        redF = Cond l <$> ctxtClosure stp f <*> return cs
        redCS = do
          let (gs,es) = unzip cs
          es' <- oneOf (ctxtClosure stp) es
          return (Cond l f (zip gs es'))
    ctxt (Abs lv le f) = Abs lv le <$> ctxtClosure stp f
    ctxt (Fix i l fs) = Fix i l <$> oneOf (ctxtClosure stp) fs
    ctxt _ = empty
    

nf :: (Monad m, Choice m) => (Exp l -> m (Exp l)) -> Exp l -> m (Exp l)
nf rel a = (rel a >>= nf rel) <||> return a

cbvCtxtClosure :: (Alternative m, Monad m, Choice m) => (Exp l -> m (Exp l)) -> Exp l -> m (Exp l)
cbvCtxtClosure stp e = ctxt e <||> stp e
  where       
    ctxt (App l e1 e2) = do
      [f1,f2] <- leftToRight (cbvCtxtClosure stp) [e1,e2]
      return (App l f1 f2)
    ctxt (Con l g es) = Con l g <$> leftToRight (cbvCtxtClosure stp) es
    ctxt (Cond l f cs) = Cond l <$> cbvCtxtClosure stp f <*> return cs
    ctxt _ = empty

cbv :: (Alternative m, Monad m, Choice m) => Exp l -> m (Exp l)
cbv = cbvCtxtClosure (\ e -> beta e <|> fixCBV e <|> cond e)

