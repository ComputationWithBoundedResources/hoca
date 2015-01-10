-- | 

module Hoca.Problem where

import qualified Data.Rewriting.Rule as R
import qualified Data.Rewriting.Rules as RS
import qualified Data.Rewriting.Problem as P
import qualified Data.IntMap as IMap
import qualified Data.IntSet as ISet
import Data.IntMap (IntMap)
import Data.IntSet (IntSet)
import qualified Hoca.PCF as PCF
import Hoca.Utils (runVarSupplyT, fresh)
import qualified Hoca.ATRS as ATRS
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Data.List (nub)
import Control.Monad.State (lift)
import Data.Maybe (catMaybes)
import Control.Applicative ((<$>), Alternative, optional, empty, pure)
import Data.Maybe (listToMaybe)

data Lbl = LString String
         | LInt Int
         deriving (Show, Eq, Ord)
                  
newtype Name = Name [Lbl] deriving (Show, Eq, Ord)

data Symbol =
  Con PCF.Symbol
  | Lambda Name
  | Bot
  | Cond Name
  | Fix Name
  | Main
  deriving (Show, Eq, Ord)

instance PP.Pretty Lbl where
  pretty (LInt i) = PP.int i
  pretty (LString i) = PP.text i


instance PP.Pretty Name where
  pretty (Name []) = PP.empty
  pretty (Name [l]) = PP.pretty l
  pretty (Name (l:ls)) = PP.pretty (Name ls) PP.<> PP.text "_" PP.<> PP.pretty l

instance PP.Pretty Symbol where
  pretty (Con g) = PP.text (PCF.sname g)
  pretty (Lambda l) = PP.pretty l
  pretty (Cond l) = PP.pretty l
  pretty (Fix l) = PP.text "rec" PP.<> PP.brackets (PP.pretty l)
  pretty Bot = PP.text "_|_"      
  pretty Main = PP.text "main"
              

type Var = Int

type Rule = ATRS.Rule Symbol Var

data Problem = Problem { pRules :: IntMap (Rule,IntSet)
                       , pSig :: Maybe (ATRS.Signature Symbol) }


instance PP.Pretty Problem where
  pretty p =
    PP.vcat $
    [ PP.int i PP.<+> PP.text ":" PP.<+> R.prettyRule (PP.text "->") PP.pretty ppVar rl | (i,(rl,_)) <- IMap.toList (pRules p) ]
    -- ++ [ PP.int i PP.<+> PP.text "~>" PP.<+> PP.hcat [ PP.int j PP.<> PP.text ";" | j <- ISet.toList js] | (i,(_,js)) <- IMap.toList (pRules p)]
    where
      ppVar i = PP.text "x" PP.<> PP.int i

toWST :: Problem -> P.Problem (ATRS.ASym Symbol) Var
toWST p = P.Problem {
  P.startTerms = P.BasicTerms
  , P.strategy = P.Innermost
  , P.theory = Nothing
  , P.rules = P.RulesPair { P.strictRules = trs, P.weakRules = [] }
  , P.variables = nub (RS.vars trs)
  , P.symbols = nub (RS.funs trs)
  , P.comment = flip PP.displayS "" <$> PP.renderSmart 1.0 75 <$> ppSig <$> pSig p }
  where
    trs = rules p
    ppSig s =
      PP.text "Types are as follows:"
      PP.</> PP.linebreak
      PP.</> PP.indent 5 (PP.align (PP.pretty s))
      PP.</> PP.linebreak

prettyWST :: Problem -> PP.Doc
prettyWST = P.prettyWST PP.pretty ppVar . toWST where
  ppVar i = PP.text "x" PP.<> PP.int i

rules :: Problem -> [Rule]
rules = map fst . IMap.elems . pRules

rulesEnum :: Problem -> [(Int,Rule)]
rulesEnum = IMap.toList . IMap.map fst . pRules

fromRules :: [Rule] -> Problem
fromRules rs =
  Problem { pRules = IMap.map (\ r -> (r,is)) (IMap.fromList irs)
          , pSig = case ATRS.inferTypes irs of
                    Left _ -> Nothing
                    Right (s,_) -> Just s }
  where
    irs = zip [1..] rs
    is = ISet.fromList (map fst irs)

withSignature :: ATRS.Signature Symbol -> Problem -> Problem
withSignature sig p = p {pSig = Just sig}

replaceRulesM :: (Monad m, Alternative m) => (Int -> Rule -> [Int] -> m [(Rule, [Int])]) -> Problem -> m Problem
replaceRulesM m p = runVarSupplyT (mapM f (IMap.toList (pRules p))) >>= toProblem 
  where
    f (i,(r,ISet.toList -> ss)) = do
      mrs <- lift (optional (m i r ss))
      case mrs of
       Nothing -> do
         j <- fresh
         return (False, (i, [(j,r,ss)]))
       Just rs -> do
         ids <- mapM (const fresh) rs
         return (True, (i, [ (j,r',ss') | (j,(r',ss')) <- zip ids rs ]))
    toProblem l
      | any fst l = pure (p { pRules = foldl ins IMap.empty (concatMap snd l') })
      | otherwise = empty
      where
        l' = map snd l
        ins is (j,r,ss) = IMap.insert j (r, newSuccs ss) is
        newSuccs = foldl (\ ss' s -> newIds s `ISet.union` ss') ISet.empty
        newIds i = 
          case lookup i l' of
           Nothing -> ISet.empty
           Just ers -> ISet.fromList [ j | (j,_,_) <- ers]

replaceRules :: (Monad m, Alternative m) => (Rule -> m [(Rule, [Int])]) -> Problem -> m Problem
replaceRules f = replaceRulesM (const (return . f))

replaceRulesIdx :: (Monad m, Alternative m) => (Int -> m [(Rule, [Int])]) -> Problem -> m Problem
replaceRulesIdx f = replaceRulesM m where
  m i _ = return (f i)

indexOf :: Problem -> Rule -> Maybe Int
indexOf p rl = listToMaybe [ i | (i,(rl',_)) <- IMap.toList (pRules p), rl == rl']

rule :: Problem -> Int -> Maybe Rule
rule p i = fst <$> IMap.lookup i (pRules p)

calleeIdxs :: Problem -> Int -> [Int]
calleeIdxs p i = maybe [] (ISet.toList . snd) (IMap.lookup i (pRules p))

callees :: Problem -> Rule -> [Rule]
callees p r =
  maybe [] (map fst . catMaybes . map (flip IMap.lookup (pRules p)) . ISet.toList)
   (lookup r (IMap.elems (pRules p)))

usableIdxs :: Problem -> [Int] -> [Int]
usableIdxs p initial = walk (concatMap (calleeIdxs p) initial) [] where
  walk [] seen = seen
  walk (i:is) seen
    | i `elem` seen = walk is seen
    | otherwise = walk (calleeIdxs p i ++ is) (i : seen)

usable :: Problem -> [Rule] -> [(Int, Rule)]
usable p rs = [(i,r) | i <- usableIdxs p (catMaybes [indexOf p rl | rl <- rs])
                     , let Just r = rule p i ]

removeUnusedRules :: Problem -> Problem
removeUnusedRules p = p { pRules = IMap.filterWithKey (\ k _ ->  (k `elem` used)) (pRules p) } where
  used = initial ++ usableIdxs p initial
  initial = [i | (i,(r,_)) <- IMap.toList (pRules p)
               , case R.lhs r of
                  R.Fun (ATRS.Sym Main) _ -> True
                  _ -> False ]

   
withEdges :: (Rule -> Rule -> Bool) -> Problem -> Problem
withEdges edgeP p = p { pRules = IMap.map f (pRules p) } where
  f (r,ss) = (r, ISet.filter (isEdge r) ss)
  isEdge r i = maybe False (edgeP r . fst) (IMap.lookup i (pRules p))


withEdgesIdx :: (Int -> Int -> Bool) -> Problem -> Problem
withEdgesIdx edgeP p = p { pRules = IMap.mapWithKey f (pRules p) } where
  f i (r,ss) = (r, ISet.filter (edgeP i) ss)

isRecursive :: Problem -> Rule -> Bool
isRecursive p rl = maybe False (isRecursiveIdx p) (indexOf p rl)

isRecursiveIdx :: Problem -> Int -> Bool
isRecursiveIdx p i = i `elem` usableIdxs p [i]