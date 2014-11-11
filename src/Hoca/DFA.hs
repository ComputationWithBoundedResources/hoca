module Hoca.DFA
       ( TGSym (..)
       , TGTerm
       , startSymbol
       , varSymbol
       , auxSymbol
       , fun
       , TGRule
       , TG
       , refinements)
       where

import qualified Data.Rewriting.Term as T
import Data.Rewriting.Term (Term (..))
import qualified Data.Rewriting.Rule as R
import qualified Data.Rewriting.Rules as RS
import qualified Data.Rewriting.Context as C
import Hoca.Utils (contexts, prod, runVarSupply, fresh)
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.List as L

import qualified Text.PrettyPrint.ANSI.Leijen as PP
import qualified Data.Rewriting.Substitution.Type as ST
import qualified Data.Rewriting.Substitution as S
import Control.Applicative ((<$>))
import Data.Maybe (fromJust)

data TGSym f v x = F f
                 | X x
                 | V v Int
                 | R Int
                 deriving (Ord, Eq, Show)

instance (PP.Pretty f, PP.Pretty v, PP.Pretty x) => PP.Pretty (TGSym f v x) where
  pretty (F s) = PP.pretty s
  pretty (X s) = PP.text "X" PP.<> PP.braces (PP.pretty s)
  pretty (V s i) = PP.text "V" PP.<> PP.braces (PP.pretty s PP.<> PP.text "_" PP.<> PP.int i) 
  pretty (R i) = PP.text "R" PP.<> PP.braces (PP.int i)
  
type TGTerm f v x = Term (TGSym f v x) ()
type TGRule f v x = R.Rule (TGSym f v x) ()

type TG f v x = [TGRule f v x]


(-->) :: Term f v -> Term f v -> R.Rule f v
(-->) = R.Rule

constant :: f -> R.Term f v
constant f = Fun f []

startSymbol :: TGTerm f v x
startSymbol = constant (R 0)

varSymbol :: v -> Int -> TGTerm f v x
varSymbol v i = constant (V v i)

auxSymbol :: x -> TGTerm f v x
auxSymbol = constant . X 

fun :: f -> [TGTerm f v x] -> TGTerm f v x
fun f = Fun (F f)


lift :: Int -> Term f v -> TGTerm f v x 
lift i (Var v) = constant (V v i)
lift i (Fun f ts) = Fun (F f) (map (lift i) ts)


minimalMatch :: (Eq f, Eq v, Eq x) => TG f v x -> Term f v -> TGTerm f v x -> [TGTerm f v x]
minimalMatch = minMatch []
  where
    minMatch _ _ (Var _) t  = [t]
    minMatch visited tg (Fun f ps) t@(Fun (F g) ts)
      | t `elem` visited = []
      | f == g = map (Fun (F g)) (prod [ minMatch [] tg p' t' | (p',t') <- zip ps ts])
      | otherwise = []
    minMatch visited tg p t
      | t `elem` visited = []
      | otherwise  = 
          concatMap (minMatch (t:visited) tg p) [ rhs | R.Rule lhs rhs <- tg, lhs == t]


epsilonNormalise :: (Eq v, Eq f, Eq x) => TG f v x -> TG f v x
epsilonNormalise tg = norm ers [] ners
  where
    (ers,ners) = L.partition epsilonRule tg
    epsilonRule rl =
      case T.root (R.rhs rl) of
       Right X{} -> True
       Right V{} -> True
       Right R{} -> True
       _ -> False
       
    norm [] _ rs = rs
    norm (e:es) seen rs
      | R.lhs e == R.rhs e = norm es seen rs
      | e `elem` seen = norm es seen rs
      | otherwise = norm (rew e es ++ es) (e:seen) (rew e rs ++ rs)

    rew (R.Rule lhs rhs) rs = [R.Rule lhs rhs' | rhs' <- rhss, rhs /= rhs']
      where rhss = map RS.result (RS.rootRewrite rs rhs)

    
complete :: (Eq x, Eq f, Eq v, Ord x, Ord f, Ord v) => [(R.Rule f v, Int)] -> TG f v x -> TG f v x
complete prog = epsilonNormalise . S.toList . iter . S.fromList
  where
    iter tg
      | tg' `S.isSubsetOf` tg  = tg
      | otherwise = iter tg'
      where
        tg' = S.fromList (step tg)
        
    step (S.toList -> tg) = concatMap (\ (R.Rule lhs rhs) -> concatMap (ext lhs tg) (contexts rhs)) tg
        
    ext lhs tg (ctxt,st) = 
      foldl (++) tg
        [ [ lhs --> (ctxt `C.apply` r), r --> lift i t ]
          ++ concat [varRules i p m | m <- ms]
        | (R.Rule p t,i) <- prog
        , let r = constant (R i)
        , let ms = minimalMatch tg p st
        , not (null ms)
        ]

    varRules i (Var x) m = [v --> m | let v = varSymbol x i,  v /= m]
    varRules i (T.Fun _ ps) (T.Fun _ ms) =
      concat [varRules i p m | (p,m) <- zip ps ms]
    varRules _ _ _ = error "DFA.varRules: pattern _ (Fun _ _) (Var _) impossible"
        

refinements :: (Ord f, Ord v, Ord x) => [R.Rule f v] -> TG f v x -> R.Rule f v -> (v -> Bool) ->  [R.Rule f Int]
refinements prog initial =
  \ rl@(R.Rule lhs rhs) refineP ->
   case L.lookup rl prog' of
    Nothing -> []
    Just i -> [R.Rule (s `apply` lhs) (s `apply` rhs) | s <- substs] 
      where
        apply s t = fromJust (S.gApply s t)
        substs = map toSubst (foldl (\ l v -> [ (v,p):s | s <- l, p <- patterns v]) [[]] (L.nub (R.vars rl)))
        patterns v
          | refineP v = L.nub (map toTerm (reducts tg (varSymbol v i)))
          | otherwise = [T.Var ()]
  where
    prog' = zip prog [1..] 
    
    tg = complete prog' initial

    toTerm (Fun (F f) ts) = Fun f (map toTerm ts)
    toTerm _ = Var ()
    
    reducts rs s = if null rhss then [s] else rhss
      where rhss = [rhs | R.Rule lhs rhs <- rs, lhs == s]

    toSubst = ST.fromMap . M.fromList . runVarSupply . mapM (\ (v,p) -> (,) v <$> ren p)
      where ren (T.Fun f ts) = T.Fun f <$> mapM ren ts
            ren _            = T.Var <$> fresh


        


