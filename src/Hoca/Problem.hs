-- | 

module Hoca.Problem where

import qualified Data.Rewriting.Applicative.Rule as R
import           Data.Rewriting.Applicative.Term as T
import qualified Data.Rewriting.Applicative.SimpleTypes as ST
import qualified Data.Rewriting.Problem as P
import qualified Data.Rewriting.Rules as RS

import           Hoca.Utils (runVarSupplyT, fresh)

import qualified Text.PrettyPrint.ANSI.Leijen as PP
import           Data.List (nub)
import qualified Data.IntMap as IMap
import qualified Data.IntSet as ISet
import           Data.IntMap (IntMap)
import           Data.IntSet (IntSet)
import           Data.Monoid (Monoid)
import           Data.Maybe (listToMaybe, catMaybes)
import           Control.Applicative ((<$>))

data Lbl = LString String
         | LInt Int
         deriving (Show, Eq, Ord)
                  
newtype Name = Name [Lbl] deriving (Show, Eq, Ord, Monoid)

data Symbol =
  Con String
  | Lambda Name
  | Bot Int
  | Cond Name
  | Fix Name
  | Main
  | Labeled Int Symbol
  deriving (Show, Eq, Ord)

instance PP.Pretty Lbl where
  pretty (LInt i) = PP.int i
  pretty (LString i) = PP.text i

instance PP.Pretty Name where
  pretty (Name []) = PP.empty
  pretty (Name [l]) = PP.pretty l
  pretty (Name (l:ls)) = PP.pretty (Name ls) PP.<> PP.text "_" PP.<> PP.pretty l

instance PP.Pretty Symbol where
  pretty (Con g) = PP.text g
  pretty (Lambda l) = PP.pretty l
  pretty (Cond l) = PP.pretty l
  pretty (Fix l) = PP.pretty l
  pretty (Bot l) = PP.text "bot" PP.<> PP.brackets (PP.pretty l)      
  pretty Main = PP.text "main"
  pretty (Labeled 0 s) = PP.pretty s
  pretty (Labeled l s) = PP.pretty s PP.<> PP.brackets (PP.int l)  


unlabeled :: Symbol -> Symbol
unlabeled (Labeled _ s) = unlabeled s
unlabeled s = s

isCaseSym,isFixSym,isMainSym,isConstructor :: Symbol -> Bool
isCaseSym f = case unlabeled f of {Cond{} -> True; _ -> False }
isFixSym f = case unlabeled f of {Fix{} -> True; _ -> False }
isMainSym f = case unlabeled f of {Main{} -> True; _ -> False }
isConstructor f = case unlabeled f of {Con{} -> True; _ -> False }


data Problem f v = Problem { pRules :: IntMap (R.ARule f v,IntSet)
                           , pSig   :: Maybe (ST.Signature f) }


instance (PP.Pretty f) => PP.Pretty (Problem f Int) where
  pretty p =
    PP.vcat
    [ PP.int i PP.<+> PP.text ":" PP.<+> R.prettyRule (PP.text "->") PP.pretty ppVar rl | (i,(rl,_)) <- IMap.toList (pRules p) ]
    where
      ppVar i = PP.text "x" PP.<> PP.int i

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
    trs = rules p

prettyWST :: (PP.Pretty f, Eq f) => Problem f Int -> PP.Doc
prettyWST = P.prettyWST PP.pretty ppVar . toWST where
  ppVar i = PP.text "x" PP.<> PP.int i

size :: Problem f v -> Int
size = IMap.size . pRules
  
rules :: Problem f v -> [R.ARule f v]
rules = map fst . IMap.elems . pRules

rulesEnum :: Problem f v -> [(Int, R.ARule f v)]
rulesEnum = IMap.toList . IMap.map fst . pRules

fromRules :: (Ord f, Ord v) => [R.ARule f v] -> Problem f v
fromRules rs =
  Problem { pRules = IMap.map (\ r -> (r,is)) (IMap.fromList irs)
          , pSig = case ST.inferTypes irs of
                    Left _ -> Nothing
                    Right (s,_) -> Just s }
  where
    irs = zip [1..] rs
    is = ISet.fromList (map fst irs)

withSignature :: ST.Signature f -> Problem f v -> Problem f v
withSignature sig p = p {pSig = Just sig}

removeInstances :: (Ord f, Ord v) => Problem f v -> Problem f v
removeInstances p = p { pRules = foldl removeInstance (pRules p) insts } where
  insts = [ (i,j) | (i,ri) <- rs, (j,rj) <- rs
                  , i /= j, ri `R.isInstanceOf` rj
                  , i < j || not (rj `R.isInstanceOf` ri) ]
    where rs = rulesEnum p
  removeInstance m (i,j) = IMap.map relink (IMap.delete i m) where
    relink (rl,ss)
      | ISet.member i ss = (rl,ISet.insert j (ISet.delete i ss))
      | otherwise = (rl,ss)

replaceRulesM :: (Monad m, Ord f, Ord v) => (Int -> R.ARule f v -> [Int] -> Maybe [(R.ARule f v, [Int])]) -> Problem f v -> m (Problem f v)
replaceRulesM m p = runVarSupplyT (mapM f (IMap.toList (pRules p))) >>= toProblem 
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
      | any fst l = return (removeInstances p { pRules = foldl ins IMap.empty (concatMap snd l') })
      | otherwise = fail "replaceRulesM"
      where
        l' = map snd l
        ins is (j,r,ss) = IMap.insert j (r, newSuccs ss) is
        newSuccs = foldl (\ ss' s -> newIds s `ISet.union` ss') ISet.empty
        newIds i = 
          case lookup i l' of
           Nothing -> ISet.empty
           Just ers -> ISet.fromList [ j | (j,_,_) <- ers]

toAssocList :: Problem f v -> [(R.ARule f v, Int, [Int])]
toAssocList p = [(i,r,ISet.toList ss) | (r,(i,ss)) <- IMap.toList (pRules p)]

replaceRules :: (Monad m, Ord f, Ord v) => (R.ARule f v -> Maybe [(R.ARule f v, [Int])]) -> Problem f v -> m (Problem f v)
replaceRules f = replaceRulesM (const (return . f))

replaceRulesIdx :: (Monad m, Ord f, Ord v) => (Int -> Maybe [(R.ARule f v, [Int])]) -> Problem f v -> m (Problem f v)
replaceRulesIdx f = replaceRulesM m where
  m i _ = return (f i)

restrictIdx :: [Int] -> Problem f v -> Problem f v
restrictIdx ixs p = p { pRules = IMap.fromList [ (i,(rl, ss `ISet.intersection` ixss))
                                               | (i,(rl,ss)) <- IMap.toList (pRules p)
                                               , i `ISet.member` ixss] } where
  ixss = ISet.fromList ixs


indexOf :: (Eq f, Eq v) => Problem f v -> R.ARule f v -> Maybe Int
indexOf p rl = listToMaybe [ i | (i,(rl',_)) <- IMap.toList (pRules p), rl == rl']

rule :: Problem f v -> Int -> Maybe (R.ARule f v)
rule p i = fst <$> IMap.lookup i (pRules p)

cgSuccs :: Problem f v -> Int -> [Int]
cgSuccs p i = maybe [] (ISet.toList . snd) (IMap.lookup i (pRules p))

cgPreds :: Problem f v -> Int -> [Int]
cgPreds p i = IMap.foldWithKey collect [] (pRules p) where
  collect j (_,ss) preds
    | i `ISet.member` ss = j : preds
    | otherwise = preds

usableIdxs :: Problem f v -> [Int] -> [Int]
usableIdxs p initial = walk (concatMap (cgSuccs p) initial) [] where
  walk [] seen = seen
  walk (i:is) seen
    | i `elem` seen = walk is seen
    | otherwise = walk (cgSuccs p i ++ is) (i : seen)

usable :: (Eq f, Eq v) => Problem f v -> [R.ARule f v] -> [(Int, R.ARule f v)]
usable p rs = [(i,r) | i <- usableIdxs p (catMaybes [indexOf p rl | rl <- rs])
                     , let Just r = rule p i ]

removeUnusedRules :: Problem Symbol v -> Problem Symbol v
removeUnusedRules p = p { pRules = IMap.filterWithKey (\ k _ ->  (k `elem` used)) (pRules p) } where
  used = initial ++ usableIdxs p initial
  initial = [i | (i,(r,_)) <- IMap.toList (pRules p)
               , case T.atermM (R.lhs r) of
                  Just (T.Fun f _) -> unlabeled f == Main
                  _ -> False ]
   
withEdges :: (R.ARule f v -> R.ARule f v -> Bool) -> Problem f v -> Problem f v
withEdges edgeP p = p { pRules = IMap.map f (pRules p) } where
  f (r,ss) = (r, ISet.filter (isEdge r) ss)
  isEdge r i = maybe False (edgeP r . fst) (IMap.lookup i (pRules p))


withEdgesIdx :: (Int -> Int -> Bool) -> Problem f v -> Problem f v
withEdgesIdx edgeP p = p { pRules = IMap.mapWithKey f (pRules p) } where
  f i (r,ss) = (r, ISet.filter (edgeP i) ss)

isRecursive :: (Eq f, Eq v) => Problem f v -> R.ARule f v -> Bool
isRecursive p rl = maybe False (isRecursiveIdx p) (indexOf p rl)

isRecursiveIdx :: Problem f v -> Int -> Bool
isRecursiveIdx p i = i `elem` usableIdxs p [i]
