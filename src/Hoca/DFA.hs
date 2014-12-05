module Hoca.DFA
       ( TGSym (..)
       , TGTerm
       , startSymbol
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
import Hoca.Utils (contexts, prod, runVarSupply, fresh, tracePretty', tracePretty)
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

pattern Data x = Fun (X x) []
pattern Substitution v i = Fun (V v i) []
pattern Result i = Fun (R i) []
pattern Term f ts = Fun (F f) ts


instance (PP.Pretty f, PP.Pretty v, PP.Pretty x) => PP.Pretty (TGSym f v x) where
  pretty (F s) = PP.pretty s
  pretty (X s) = PP.text "X" PP.<> PP.braces (PP.pretty s)
  pretty (V s i) = PP.text "V" PP.<> PP.braces (PP.text "x" PP.<> PP.pretty s PP.<> PP.text "_" PP.<> PP.int i) 
  pretty (R i) = PP.text "R" PP.<> PP.braces (PP.int i)
  
type TGTerm f v x = Term (TGSym f v x) ()
type TGRule f v x = R.Rule (TGSym f v x) ()

type TG f v x = [TGRule f v x]

(-->) :: Term f v -> Term f v -> R.Rule f v
(-->) = R.Rule

-- constant :: f -> R.Term f v
-- constant f = Fun f []

startSymbol :: TGTerm f v x
startSymbol = Result 0

auxSymbol :: x -> TGTerm f v x
auxSymbol = Data

fun :: f -> [TGTerm f v x] -> TGTerm f v x
fun f = Fun (F f)


lift :: Int -> Term f v -> TGTerm f v x 
lift i (Var v) = Substitution v i
lift i (Fun f ts) = Term f (map (lift i) ts)

unlift :: TGTerm f v x -> Term f ()
unlift (Term f ts) = Fun f (map unlift ts)
unlift _ = Var ()
    
-- TODO
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

-- minimalMatch :: (Ord v, Eq f, Eq v, Eq x, PP.Pretty x, PP.Pretty f, PP.Pretty v) => [(R.Rule f v, Int)] -> TG f v x -> Term f v -> TGTerm f v x -> [TGTerm f v x]
minimalMatch tg t1 t2 = let mm = minMatch [] t1 t2 in mm
  where
    minMatch _ (Var _) t  = [t]
    minMatch visited (Fun f ps) t@(Term g ts)
      | t `elem` visited = []
      | f == g = map (Term g) (prod [ minMatch [] p' t' | (p',t') <- zip ps ts])
      | otherwise = []
    minMatch visited p t
      | t `elem` visited = []
      | otherwise  = 
          concatMap (minMatch (t:visited) p) [ rhs | R.Rule lhs rhs <- tg, lhs == t]



complete :: (Eq x, Eq f, Eq v, Ord x, Ord f, Ord v,PP.Pretty x, PP.Pretty f, PP.Pretty v) => [(R.Rule f v, Int)] -> TG f v x -> TG f v x
complete prog = epsilonNormalise . S.toList . iter . S.fromList . tracePretty' 
  where
    iter tg
      | tg' `S.isSubsetOf` tg  = tg
      | otherwise = tracePretty (S.toList (tg' S.\\ tg)) (iter tg')
      where
        tg' = S.fromList (step tg)
        
    step (S.toList -> tg) = tg ++ concatMap (\ (R.Rule lhs rhs) -> concatMap (ext lhs) (contexts (annotateMatches tg rhs))) tg

    ext lhs (ctxt, st) =
      concat [
        [ lhs --> dropAnnotations (ctxt `C.apply` Fun (R i,[]) [])
        , Result i --> lift i t ]
        ++ concat [varRules i p m | m <- ms]
        | (R.Rule p t, i ,ms) <- minimalMatches st ]
      

    minimalMatches (Fun (_,a) _) = a
    minimalMatches _ = []
    dropAnnotations = T.map fst id
    annotateMatches _  (Var v) = Var v
    annotateMatches tg t@(Fun f ts) = Fun (f,a) ts' where
      ts' = map (annotateMatches tg) ts
      a = case f of
        (F _) | normalised -> [ (R.Rule l r, i, ms) | (R.Rule l r,i) <- prog, let ms = minimalMatch tg l t, not (null ms)]
        _ -> []
      normalised = all (null . minimalMatches) (concatMap T.subterms ts')
    
    varRules i (Var x) m = [ v --> m | let v = Substitution x i,  v /= m]
    varRules i (Fun _ ps) (Fun _ ms) =
      concat [varRules i p m | (p,m) <- zip ps ms]
      
    varRules _ _ _ = error "DFA.varRules: pattern _ (Fun _ _) (Var _) impossible"
        

--refinements :: (Ord f, Ord v, Ord x) => [R.Rule f v] -> TG f v x -> R.Rule f v -> (v -> Bool) ->  [R.Rule f Int]
refinements prog initial =
  \ rl@(R.Rule lhs rhs) refineP ->
   case L.lookup rl prog' of
    Nothing -> []
    Just i
      | ruleReachable -> [R.Rule (s `apply` lhs) (s `apply` rhs) | s <- substs]
      | otherwise -> []
      where
        apply s t = fromJust (S.gApply s t)
        substs = map toSubst (foldl (\ l v -> [ (v,p):s | s <- l, p <- patterns v]) [[]] (L.nub (R.vars rl))) where 
          patterns v
            | refineP v = L.nub (map unlift (reducts tg (Substitution v i)))
            | otherwise = [T.Var ()]
        ruleReachable = any (== Result i) (RS.lhss tg)
  where
    prog' = tracePretty' (zip prog [1..] )
    
    tg = complete prog' initial

    reducts rs s = if null rhss then [s] else rhss
      where rhss = [rhs | R.Rule lhs rhs <- rs, lhs == s]

    toSubst = ST.fromMap . M.fromList . runVarSupply . mapM (\ (v,p) -> (,) v <$> ren p)
      where
        ren (T.Fun f ts) = T.Fun f <$> mapM ren ts
        ren _            = T.Var <$> fresh


        


