-- | 

module Hoca.PCF2Trs (
  Symbol (..)
  , Term
  , Rule
  , Problem
  , toProblem
  , prettyProblem
  , simplify
  ) where

import           Control.Applicative ((<$>))
import           Control.Monad.Writer.Lazy as W
import qualified Data.IntSet as Set
import           Data.List (sort, nub)
import Data.Either (partitionEithers)
import Data.Maybe (listToMaybe, fromJust)
import qualified Data.Map as Map
import qualified Data.Rewriting.Problem as P
import qualified Data.Rewriting.Rule as R
import qualified Data.Rewriting.Rules as RS
import qualified Data.Rewriting.Substitution as S
import qualified Data.Rewriting.Substitution.Type as ST
import qualified Data.Rewriting.Term as T
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import qualified Hoca.PCF as PCF
import Hoca.UsableRules (usableRules)
import Hoca.Narrowing

type Var = Int

data Symbol =
  Con PCF.Symbol
  | Lambda PCF.Exp
  | Bot
  | App
  | Cond PCF.Exp [(PCF.Symbol, PCF.Exp)]
  | Fix PCF.Exp
  | Main
    deriving (Show, Eq)

type Term = T.Term Symbol Var
type Rule = R.Rule Symbol Var
type Problem = P.Problem Symbol Var


(-->) :: T.Term f v -> T.Term f v -> R.Rule f v
(-->) = R.Rule

app :: T.Term Symbol v -> T.Term Symbol v -> T.Term Symbol v
app t1 t2 = T.Fun App [t1,t2]

prettyProblem :: Problem -> PP.Doc
prettyProblem = P.prettyWST ppFun ppVar
    where
      ppFun (Con g) = ppSym g
      ppFun (Lambda e) = PP.text "L" PP.<> PP.braces (ppExp e)
      ppFun App = PP.text "@"
      ppFun (Cond e cs) = PP.text "C" PP.<> PP.braces (ppCond e cs)
      ppFun (Fix e) = PP.text "FIX" PP.<> PP.braces (ppExp e)
      ppFun Bot = PP.text "_|_"      
      ppFun Main = PP.text "main"
      
      ppVar i = PP.text "x" PP.<> PP.int i

      ppExp (PCF.Var i) = PP.int i
      ppExp (PCF.Con f as) =
        ppSym f PP.<> PP.brackets (PP.hcat (PP.punctuate (PP.text "*") [ppExp ai | ai <- as]))
      ppExp PCF.Bot = PP.text "_|_"
      ppExp (PCF.Abs _ e) =
        PP.text "L" PP.<> PP.brackets (ppExp e)
      ppExp (PCF.App e1 e2) =
        PP.brackets (ppExp e1 PP.<> PP.text "." PP.<> ppExp e2)
      ppExp (PCF.Fix e) =
        PP.text "FIX" PP.<> PP.brackets (ppExp e)
      ppExp (PCF.Cond e cs) =
        PP.text "C" PP.<> 
        PP.brackets (ppCond e cs)

      ppCond e cs =
        ppExp e PP.<> PP.text ";"
        PP.<> PP.hcat [ ppSym g PP.<> PP.text ":" PP.<> ppExp e' <> PP.text ";" | (g,e') <- cs ]
      ppSym = PP.text . PCF.sname
      
toProblem :: PCF.Exp -> Problem
toProblem e = P.Problem {
  P.startTerms = P.BasicTerms
  , P.strategy = P.Innermost
  , P.theory = Nothing
  , P.rules = P.RulesPair { P.strictRules = trs, P.weakRules = [] }
  , P.variables = nub (RS.vars trs)
  , P.symbols = nub (RS.funs trs)
  , P.comment = Nothing }
  where
    trs = toTRS e
    
toTRS :: PCF.Exp -> [Rule]
toTRS = toTRS' []
  where
    freshVars [] = [0..]
    freshVars (v:_) = [v+1..]
    freshVar = head . freshVars
    
    var = T.Var
    cvars = map var . sort . Set.toList
    
    toTRS' vs (PCF.Abs _ f) = toTRS' (freshVar vs:vs) f
    toTRS' vs e =
      W.execWriter $ do
        (e',fvars) <- toTRSM vs e
        W.tell [T.Fun Main (cvars fvars) --> e' ]

    toTRSM vs (PCF.Var i) = return (var v,Set.singleton v)
      where v = vs!!i

    toTRSM vs (PCF.Abs _ f) = do
      let v' = freshVar vs
      (tf,fvarsf) <- toTRSM (v':vs) f
      let
        fvars = Set.delete v' fvarsf
        te = T.Fun (Lambda f) (cvars fvars)
      tell [ app te (var v') --> tf ]
      return (te, fvars)

    toTRSM vs (PCF.App e1 e2) = do
      (e1',fvars1) <- toTRSM vs e1
      (e2', fvars2) <- toTRSM vs e2
      return (app e1' e2', fvars1 `Set.union` fvars2)

    toTRSM vs (PCF.Con g es) = do
      (es',fvars) <- unzip <$> mapM (toTRSM vs) es
      return (T.Fun (Con g) es', Set.unions fvars)
      
    toTRSM _ PCF.Bot = return (T.Fun Bot [], Set.empty)
    
    toTRSM vs (PCF.Cond f cs) = do
      
      (tf,fvarsf) <- toTRSM vs f
      
      let caseBdy 0 fg = fg
          caseBdy (n+1) (PCF.Abs _ fg) = caseBdy n fg
          caseBdy _ _ = error "case expression with invalid body"
          
      cs' <- forM cs $ \ (g,fg) -> do
        let vs' = take (PCF.sarity g) (freshVars vs)
        (tg, fvarsg) <- toTRSM (reverse vs' ++ vs) (caseBdy (PCF.sarity g) fg)
        return (g, tg, vs', fvarsg Set.\\ Set.fromList vs')
        
      let fvars = Set.unions [ fvarsg | (_,_,_,fvarsg) <- cs' ]
          cond t = T.Fun (Cond f cs) (t : cvars fvars)
          
      tell [ cond (T.Fun (Con g) vars) --> tg | (g,tg,vs',_) <- cs' , let vars = map var vs' ]
      return (cond tf, fvarsf `Set.union` fvars)

    toTRSM vs (PCF.Fix (PCF.Abs _ b)) = do
      let v = freshVar vs
      (tb,fvarsb) <- toTRSM (v:vs) b
      let
        fvars = Set.delete v fvarsb
        tf = T.Fun (Fix b) (cvars fvars)
        subst = ST.fromMap (Map.singleton v tf)
      tell [ app tf (var v) --> app (S.apply subst tb) (var v) ]
      return (tf,fvars)
    toTRSM _ (PCF.Fix _) =
      error "non-lambda abstraction given to fixpoint combinator"
      
    -- toTRSM vs (PCF.Fix e) = do
    --   (te,fvars) <- toTRSM vs e
    --   let tf  = T.Fun Fix [te]
    --   tell [ app tf (fvar 0) --> app (app te tf) (fvar 0) ]
    --   return (tf,fvars)
      
-- simplification ---------------------------------------------------------------------


iter :: (a -> Maybe a) -> a -> a
iter f a = case f a of { Nothing -> a; Just b -> iter f b }

renameRule :: R.Rule f (Either Var Var) -> R.Rule f Var
renameRule rl = R.rename f rl
  where
    f = either (\ v -> fromJust (lookup v lvs)) id
    lhs = R.lhs rl
    lvs = foldl insrt [(v,v) | Right v <- T.vars lhs] [v | Left v <- T.vars lhs]
    insrt vs v = (v, head (dropWhile (`elem` map snd vs) [v..])):vs
    

isCaseRule :: R.Rule Symbol v -> Bool
isCaseRule rl =
  case T.root (R.lhs rl) of {Right Cond{} -> True; _ -> False}

isLambdaApplication :: R.Rule Symbol v -> Bool
isLambdaApplication rl =
  case R.lhs rl of
   T.Fun App [T.Fun (Lambda _) _, _] -> True
   _ -> False

simplify :: Problem -> Problem
simplify prob =
  prob { P.rules = P.RulesPair { P.strictRules = simplifiedTrs
                               , P.weakRules = []}
       , P.variables = nub (RS.vars simplifiedTrs)
       , P.symbols = nub (RS.funs simplifiedTrs) }
  where
    
    trs = P.strictRules (P.rules prob) ++ P.weakRules (P.rules prob)
    
    simplifiedTrs = iter narrowRules trs

    mains = [t | t@(T.Fun Main _) <- RS.lhss trs]

    sound rs nr =
      case narrowSubterm nr of
       T.Fun _ ts -> null (usableRules ts rs)
       _ -> False
               
    sensible nr =
      all (\ nw -> isCaseRule nw
                   || isLambdaApplication nw)
      (map narrowedWith (narrowings nr))
      
    narrowRules rs =
      case partitionEithers (map (narrowRule rs) rs) of
       (_,[]) -> Nothing 
       (untransformed,transformed) ->
         Just (usableRules mains rs')
         where 
           rs' = untransformed ++ concat transformed

    narrowRule rs r = 
      case listToMaybe [ ni | ni <- narrow r rs, sound rs ni, sensible ni ] of
       Nothing -> Left r
       Just ni -> Right [renameRule (narrowing n) | n <- narrowings ni]



