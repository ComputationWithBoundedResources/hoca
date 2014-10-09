-- | 

module Hoca.PCF2Trs (
  toProblem
  , prettyProblem
  , Symbol (..)
  , Term
  , Rule
  , Problem
  )

       where

import           Control.Applicative ((<$>))
import           Control.Monad.Writer.Lazy as W
import qualified Data.IntSet as Set
import           Data.List (sort, nub)
import qualified Data.Map as Map
import qualified Data.Rewriting.Problem as P
import qualified Data.Rewriting.Rule as R
import qualified Data.Rewriting.Rules as RS
import qualified Data.Rewriting.Substitution as S
import qualified Data.Rewriting.Substitution.Type as ST
import qualified Data.Rewriting.Term as T
import qualified Hoca.PCF as PCF
import qualified Text.PrettyPrint.ANSI.Leijen as PP

data Symbol e =
  Constr PCF.Symbol
  | Lambda e
  | Bot
  | App
  | Cond e [(PCF.Symbol, e)]
  | Fix e
  | Main
    deriving (Show, Eq)
             
    
data Var =
  ClosureVar Int
  | FVar Int
    deriving (Show, Eq, Ord)

type Term e = T.Term (Symbol e) Var
type Rule e = R.Rule (Symbol e) Var

(-->) :: Term e -> Term e -> Rule e
(-->) = R.Rule

app :: T.Term (Symbol e) v -> T.Term (Symbol e) v -> T.Term (Symbol e) v
app t1 t2 = T.Fun App [t1,t2]


type Problem e = P.Problem (Symbol e) Var

prettyProblem :: Problem PCF.Exp -> PP.Doc
prettyProblem = P.prettyWST ppFun ppVar
    where
      ppFun (Constr g) = ppSym g
      ppFun (Lambda e) = PP.text "L" PP.<> PP.braces (ppExp e)
      ppFun App = PP.text "@"
      ppFun (Cond e cs) = PP.text "C" PP.<> PP.braces (ppCond e cs)
      ppFun (Fix e) = PP.text "FIX" PP.<> PP.braces (ppExp e)
      ppFun Bot = PP.text "_|_"      
      ppFun Main = PP.text "main"
      
      ppVar (ClosureVar i) = PP.text "x" PP.<> PP.int i
      ppVar (FVar i) = PP.text "y" PP.<> PP.int i      

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
      
toProblem :: PCF.Exp -> Problem PCF.Exp
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
    
toTRS :: PCF.Exp -> [Rule PCF.Exp]
toTRS = toTRS' []
  where
    freshVars [] = [0..]
    freshVars (v:_) = [v+1..]

    cvar = T.Var . ClosureVar
    cvars = map cvar . sort . Set.toList
    
--    fvar = T.Var . FVar
    
    toTRS' vs (PCF.Abs _ f) = toTRS' (head (freshVars vs):vs) f
    toTRS' vs e =
      W.execWriter $ do
        (e',fvars) <- toTRSM vs e
        W.tell [T.Fun Main (cvars fvars) --> e' ]

    toTRSM vs (PCF.Var i) = return (cvar v,Set.singleton v)
      where v = vs!!i

    toTRSM vs (PCF.Abs _ f) = do
      let v' = head (freshVars vs)
      (tf,fvarsf) <- toTRSM (v':vs) f
      let
        fvars = Set.delete v' fvarsf
        te = T.Fun (Lambda f) (cvars fvars)
      tell [ app te (cvar v') --> tf ]
      return (te, fvars)

    toTRSM vs (PCF.App e1 e2) = do
      (e1',fvars1) <- toTRSM vs e1
      (e2', fvars2) <- toTRSM vs e2
      return (app e1' e2', fvars1 `Set.union` fvars2)

    toTRSM vs (PCF.Con g es) = do
      (es',fvars) <- unzip <$> mapM (toTRSM vs) es
      return (T.Fun (Constr g) es', Set.unions fvars)
      
    toTRSM _ PCF.Bot = return (T.Fun Bot [], Set.empty)
    
    toTRSM vs (PCF.Cond f cs) = do
      (tf,fvarsf) <- toTRSM vs f
      let caseBdy 0 fg = fg
          caseBdy (n+1) (PCF.Abs _ fg) = caseBdy n fg
          caseBdy _ _ = error "case expression with invalid body"
          
      cs' <- forM cs $ \ (g,fg) -> do
        let ar = PCF.sarity g
            vs' = take ar (freshVars vs)
        (tg, fvarsg) <- toTRSM (reverse vs' ++ vs) (caseBdy ar fg)
        return (g, tg, vs', fvarsg Set.\\ Set.fromList vs')
      let fvars = Set.unions [ fvarsg | (_,_,_,fvarsg) <- cs' ]
          cond t = T.Fun (Cond f cs) (t : cvars fvars)
          rs = [ cond (T.Fun (Constr g) vars) --> tg
               | (g,tg,vs',_) <- cs' , let vars = map cvar vs' ]
      tell rs
      return (cond tf, fvarsf `Set.union` fvars)

    toTRSM vs (PCF.Fix (PCF.Abs _ b)) = do
      let v = head (freshVars vs)
      (tb,fvarsb) <- toTRSM (v:vs) b
      let
        fvars = Set.delete v fvarsb
        tf = T.Fun (Fix b) (cvars fvars)
        subst = ST.fromMap (Map.singleton (ClosureVar v) tf)
      tell [ app tf (cvar v) --> app (S.apply subst tb) (cvar v) ]
      return (tf,fvars)
    toTRSM _ (PCF.Fix _) =
      error "non-lambda abstraction given to fixpoint combinator"
      
    -- toTRSM vs (PCF.Fix e) = do
    --   (te,fvars) <- toTRSM vs e
    --   let tf  = T.Fun Fix [te]
    --   tell [ app tf (fvar 0) --> app (app te tf) (fvar 0) ]
    --   return (tf,fvars)
      
