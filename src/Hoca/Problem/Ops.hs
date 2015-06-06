-- | 

module Hoca.Problem.Ops (
  -- * Problems     
  rules
  , fromRules
  , fromGraph
  , rulesEnum
  , size
  , funs
  , leftHandSides
  , rightHandSides
  -- ** Call Graph Operations
  , rule
  , toAssocList
  , indexOf
  , cgSuccs
  , cgPreds
  -- , usable
  , usableIdx
  -- , isRecursive
  -- , isRecursiveIdx
  -- ** Traversal and Modification
  , restrictIdx
  , removeUnusedRules
  , replaceRules
  , replaceRulesIdx
  , withEdges
  , withEdgesIdx
  , modifyMains
  , modifySignature
  -- * Typed Rules
  , renameTRule
  , (|-)
  , tvsFromTRule
) where

import           Control.Arrow (first, second)
import qualified Data.IntMap as IMap
import qualified Data.IntSet as ISet
import           Data.Maybe (listToMaybe)
import qualified Data.Rewriting.Applicative.Rule as R
import qualified Data.Rewriting.Applicative.Term as T
import qualified Data.Rewriting.Rules as RS
import           Hoca.Data.MLTypes (Signature, Type, TypeVariable,tvs)
import           Hoca.Problem.Type
import           Hoca.Utils (runVarSupplyT, fresh)

renameTRule :: (v -> v') -> TRule f v -> TRule f v'
renameTRule f tr = 
  TRule { theRule = R.mapRule (T.amap id f) (theRule tr) 
        , theEnv = map (first f) (theEnv tr)
        , theType = theType tr }

tvsFromTRule :: TRule f v -> [TypeVariable]
tvsFromTRule trl = concatMap tvs (theType trl : map snd (theEnv trl))

(|-) :: TypingEnv v -> (R.ARule f v, Type) -> TRule f v
env |- (rl,tp) = TRule rl env tp


size :: Problem f v -> Int
size = IMap.size . ruleGraph
  
rules :: Problem f v -> [TRule f v]
rules = map fst . IMap.elems . ruleGraph

rulesEnum :: Problem f v -> [(Int, TRule f v)]
rulesEnum = IMap.toList . IMap.map fst . ruleGraph

fromRules :: (Ord f, Ord v) => [f] -> Signature f -> [TRule f v] -> Problem f v
fromRules fs sig rs = 
  Problem { ruleGraph = IMap.map (\ r -> (r,is)) (IMap.fromList irs)
          , mains = fs
          , signature = sig } where
    irs = zip [1..] rs
    is = ISet.fromList (map fst irs)

fromGraph :: [f] -> Signature f -> [(Int,TRule f v)] -> (Int -> Int -> Bool) -> Problem f v
fromGraph fs sig ns edgeP = 
  Problem { ruleGraph = IMap.fromList [ (n, (trl, ISet.fromList [ m | m <- idxs, edgeP n m]))
                                      | (n,trl) <- ns ] 
          , mains = fs
          , signature = sig } where
    idxs = map fst ns

funs :: Problem f v -> [(f,Int)]
funs rs = [ (f,n) 
          | (T.Sym f, n) <- RS.funs ((R.mapRule T.withArity . theRule) `map` rules rs)]
          
leftHandSides :: Problem f v -> [T.ATerm f v]
leftHandSides = map (R.lhs . theRule) . rules

rightHandSides :: Problem f v -> [T.ATerm f v] 
rightHandSides = map (R.rhs . theRule) . rules 

modifySignature :: (Signature f -> Signature f) -> Problem f v -> Problem f v 
modifySignature f p = p { signature = f (signature p)}

modifyMains :: ([f] -> [f]) -> Problem f v -> Problem f v 
modifyMains f p = p { mains = f (mains p)}

---------------------------------------------------------------------- 
-- graph ops
---------------------------------------------------------------------- 

modifyRuleGraph :: (RuleGraph f v -> RuleGraph f v) -> Problem f v -> Problem f v
modifyRuleGraph f p = p { ruleGraph = f (ruleGraph p) }

restrictIdx :: [Int] -> Problem f v -> Problem f v
restrictIdx ixs = modifyRuleGraph restrict where
  restrict rg = IMap.fromList [ (i,(rl, ss `ISet.intersection` ixss))
                              | (i,(rl,ss)) <- IMap.toList rg
                              , i `ISet.member` ixss]
  ixss = ISet.fromList ixs


indexOf :: (Eq f, Eq v) => Problem f v -> R.ARule f v -> Maybe Int
indexOf p rl = listToMaybe [ i | (i,(rl',_)) <- IMap.toList (ruleGraph p), rl == theRule rl']

rule :: Problem f v -> Int -> Maybe (TRule f v)
rule p i = fst <$> IMap.lookup i (ruleGraph p)

cgSuccs :: Problem f v -> Int -> [Int]
cgSuccs p i = maybe [] (ISet.toList . snd) (IMap.lookup i (ruleGraph p))

cgPreds :: Problem f v -> Int -> [Int]
cgPreds p i = IMap.foldWithKey collect [] (ruleGraph p) where
  collect j (_,ss) preds
    | i `ISet.member` ss = j : preds
    | otherwise = preds

usableIdx :: Problem f v -> [Int] -> [Int]
usableIdx p initial = walk (concatMap (cgSuccs p) initial) [] where
  walk [] seen = seen
  walk (i:is) seen
    | i `elem` seen = walk is seen
    | otherwise = walk (cgSuccs p i ++ is) (i : seen)

-- usable :: (Eq f, Eq v) => Problem f v -> [R.ARule f v] -> [(Int, R.ARule f v)]
-- usable p rs = [(i,r) | i <- usableIdx p (catMaybes [indexOf p rl | rl <- rs])
--                      , let Just r = rule p i ]


-- isRecursive :: (Eq f, Eq v) => Problem f v -> R.ARule f v -> Bool
-- isRecursive p rl = maybe False (isRecursiveIdx p) (indexOf p rl)

-- isRecursiveIdx :: Problem f v -> Int -> Bool
-- isRecursiveIdx p i = i `elem` usableIdx p [i]

---------------------------------------------------------------------- 
-- auxiliary
---------------------------------------------------------------------- 


toAssocList :: Problem f v -> [(TRule f v, Int, [Int])]
toAssocList p = [(i,r,ISet.toList ss) | (r,(i,ss)) <- IMap.toList (ruleGraph p)]

removeUnusedRules :: Eq f => Problem f v -> Problem f v
removeUnusedRules p = modifyRuleGraph (IMap.filterWithKey (\ k _ ->  (k `elem` used))) p where
  used = initial ++ usableIdx p initial
  initial = [i | (i,(r,_)) <- IMap.toList (ruleGraph p)
               , case T.atermM (R.lhs (theRule r)) of
                  Just (T.TFun f _) -> f `elem` mains p
                  _ -> False ]
                  
removeInstances :: (Ord f, Ord v) => Problem f v -> Problem f v
removeInstances p = modifyRuleGraph remv p where 
  rs = map (second theRule) (rulesEnum p)
  remv rg = foldl removeInstance rg insts
  insts = [ (i,j) | (i,ri) <- rs, (j,rj) <- rs
                  , i /= j, ri `R.isInstanceOf` rj
                  , i < j || not (rj `R.isInstanceOf` ri) ]
  removeInstance m (i,j) = IMap.map relink (IMap.delete i m) where
    relink (rl,ss)
      | ISet.member i ss = (rl,ISet.insert j (ISet.delete i ss))
      | otherwise = (rl,ss)

withEdges :: (TRule f v -> TRule f v -> Bool) -> Problem f v -> Problem f v
withEdges edgeP = modifyRuleGraph we where
  we rg = IMap.map f rg where
    f (r,ss) = (r, ISet.filter (isEdge r) ss)
    isEdge r i = maybe False (edgeP r . fst) (IMap.lookup i rg)


withEdgesIdx :: (Int -> Int -> Bool) -> Problem f v -> Problem f v
withEdgesIdx edgeP = modifyRuleGraph (IMap.mapWithKey f) where
  f i (r,ss) = (r, ISet.filter (edgeP i) ss)



---------------------------------------------------------------------- 
-- traversal
---------------------------------------------------------------------- 


replaceRulesIdx :: (Monad m, Ord f, Ord v) => (Int -> TRule f v -> [Int] -> Maybe [(TRule f v, [Int])]) -> Problem f v -> m (Problem f v)
replaceRulesIdx m p = runVarSupplyT (mapM f (IMap.toList (ruleGraph p))) >>= toProblem 
  where
    f (i,(r,ISet.toList -> ss)) = 
      case m i r ss of
       Nothing -> do
         j <- fresh
         return (False, (i, [(j,r,ss)]))
       Just rs -> do
         ids <- mapM (const fresh) rs
         return (True, (i, [ (j,r',ss') | (j,(r',ss')) <- zip ids rs ]))

    toProblem l
      | any fst l = return (removeUnusedRules (removeInstances (modifyRuleGraph (const rg) p)))
      | otherwise = fail "Hoca.Problem.replaceRulesIdx"
      where
        rg = foldl ins IMap.empty (concatMap snd l')
        l' = map snd l
        ins is (j,r,ss) = IMap.insert j (r, newSuccs ss) is
        newSuccs = foldl (\ ss' s -> newIds s `ISet.union` ss') ISet.empty
        newIds i = 
          case lookup i l' of
           Nothing -> ISet.empty
           Just ers -> ISet.fromList [ j | (j,_,_) <- ers]

replaceRules :: (Monad m, Ord f, Ord v) => (TRule f v -> Maybe [(TRule f v, [Int])]) -> Problem f v -> m (Problem f v)
replaceRules f = replaceRulesIdx (\ _ r _ -> f r)
