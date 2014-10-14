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

import           Control.Applicative ((<$>),(<*>),(<|>), Alternative, empty, pure)
import           Control.Monad.Writer.Lazy as W
import qualified Control.Monad.State.Lazy as State
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
import qualified Hoca.UsableRules as UR
import Hoca.Narrowing
type Var = Int

data Lbl = LString String
         | LInt Int
         deriving (Show, Eq)
                  
type Label = [Lbl]

data Symbol =
  Con PCF.Symbol
  | Lambda (Maybe Label) (PCF.Exp Label)
  | Bot
  | App
  | Cond (PCF.Exp Label) [(PCF.Symbol, PCF.Exp Label)]
  | Fix (Maybe Label) (PCF.Exp Label)
  | Main
    deriving (Show, Eq)


instance PP.Pretty Lbl where
  pretty (LInt i) = PP.int i
  pretty (LString i) = PP.text i

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
      ppFun (Lambda Nothing e) = PP.text "L" PP.<> PP.braces (ppExp e)
      ppFun (Lambda (Just l) _) = ppLab l
      ppFun App = PP.text "@"
      ppFun (Cond e cs) = PP.text "C" PP.<> PP.braces (ppCond e cs)
      ppFun (Fix Nothing e) = PP.text "F" PP.<> PP.braces (ppExp e)
      ppFun (Fix (Just l) _) = ppLab l
      ppFun Bot = PP.text "_|_"      
      ppFun Main = PP.text "main"

      ppLab [] = PP.empty
      ppLab [l] = PP.pretty l
      ppLab (l:ls) = ppLab ls PP.<> PP.text "_" PP.<> PP.pretty l
      
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
      
toProblem :: PCF.Exp String -> Problem
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

label :: PCF.Exp String -> PCF.Exp Label
label e = State.evalState (labelM e) []
  where
    labelM (PCF.Var v) = return (PCF.Var v)
    labelM (PCF.Con g es) = PCF.Con g <$> mapM labelM es
    labelM PCF.Bot = return PCF.Bot
    labelM (PCF.Abs Nothing e1) = PCF.Abs Nothing <$> labelM e1
    labelM (PCF.Abs (Just l) e1) = PCF.Abs <$> (Just <$> fresh [LString l]) <*> labelM e1
    labelM (PCF.App e1 e2) = PCF.App <$> labelM e1 <*> labelM e2
    labelM (PCF.Cond e1 cs) =
      PCF.Cond <$> labelM e1 <*> mapM (\ (g,eg) -> (,) g <$> labelM eg) cs
    labelM (PCF.Fix (PCF.Abs (Just l) e1)) = do
      lfx <- fresh [LString l]
      e1' <- labelBdyM lfx [LString "cl"] e1
      return (PCF.Fix (PCF.Abs (Just lfx) e1'))
    labelM (PCF.Fix e1) = PCF.Fix <$> labelM e1
    
    labelBdyM l1 l2 (PCF.Abs (Just l3) e1) = do
      l' <- fresh (l2 ++ l1)
      PCF.Abs (Just l') <$> labelBdyM l' [LString l3] e1
    labelBdyM _ _ e1 = labelM e1        
      
    fresh :: Label -> State.State [Label] Label
    fresh l = do 
      seen <- State.get
      let
        inc (LInt i :ls) = (LInt (i+1) :ls)
        inc vs = LInt 1:vs
        v = head (dropWhile (`elem` seen) (iterate inc l))
      State.put (v:seen)
      return v
        
        

toTRS :: PCF.Exp String -> [Rule]
toTRS = toTRS' [] . label
  where
    freshVars [] = [0..]
    freshVars (v:_) = [v+1..]
    freshVar = head . freshVars
    
    var = T.Var
    cvars = map var . sort . Set.toList
    
    toTRS' vs (PCF.Abs _ f) = toTRS' (freshVar vs:vs) f
    toTRS' vs e =
      W.execWriter $ do
        (e',_) <- toTRSM vs e
        W.tell [T.Fun Main (map T.Var (sort vs)) --> e' ]

    toTRSM vs (PCF.Var i) = return (var v,Set.singleton v)
      -- (e1',fvars1) <- toTRSM vs e1
      -- (e2', fvars2) <- toTRSM vs e2
      -- return (app e1' e2', fvars1 `Set.union` fvars2)
      where v = vs!!i

    toTRSM vs (PCF.Abs l f) = do
      let v' = freshVar vs
      (tf,fvarsf) <- toTRSM (v':vs) f
      let
        fvars = Set.delete v' fvarsf
        te = T.Fun (Lambda l f) (cvars fvars)
      tell [ app te (var v') --> tf ]
      return (te, fvars)

    toTRSM vs (PCF.App e1 e2) = do
      (e1',fvars1) <- toTRSM vs e1
      (e2', fvars2) <- toTRSM vs e2
      return (app e1' e2', fvars1 `Set.union` fvars2)
      -- case flatten e of
      --  Just (f,es) -> do
      --    let vs' = take (length es) (freshVars vs)
      --    (tf,fvarsf) <- toTRSM (reverse vs' ++ vs) f
      --    (tes,fvarsas) <- unzip <$> mapM (toTRSM vs) es
      --    let subst = ST.fromMap (Map.fromList (zip vs' tes))
      --    return (S.apply subst tf, Set.unions (fvarsf:fvarsas))
      --  Nothing -> do
      --    (e1',fvars1) <- toTRSM vs e1
      --    (e2', fvars2) <- toTRSM vs e2
      --    return (app e1' e2', fvars1 `Set.union` fvars2)
      -- where
      --   flatten (PCF.App f1 f2) =
      --     case flatten f1 of
      --      Just (PCF.Abs _ f1', es) -> Just (f1',es ++ [f2])
      --      _ -> Nothing
      --   flatten f = Just (f,[])
        

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

    toTRSM vs (PCF.Fix (PCF.Abs l b)) = do
      let v = freshVar vs
      (tb,fvarsb) <- toTRSM (v:vs) b
      let
        fvars = Set.delete v fvarsb
        tf = T.Fun (Fix l b) (cvars fvars)
        subst = ST.fromMap (Map.singleton v tf)
      tell [ app tf (var v) --> app (S.apply subst tb) (var v) ]
      return (tf,fvars)
    toTRSM _ (PCF.Fix _) =
      error "non-lambda abstraction given to fixpoint combinator"
      
-- simplification ---------------------------------------------------------------------


definedSymbol :: R.Rule Symbol v -> Symbol
definedSymbol rl = case R.lhs rl of
  T.Fun App [T.Fun s _, _] -> s
  T.Fun s _ -> s
  _ -> error "PCF2Trs.definedSymbols: rule defines variable"

isCaseRule :: R.Rule Symbol v -> Bool
isCaseRule rl =
  case definedSymbol rl of {Cond{} -> True; _ -> False}

isLambdaApplication :: R.Rule Symbol v -> Bool
isLambdaApplication rl =
  case definedSymbol rl of {Lambda{} -> True; _ -> False}

isFixApplication :: R.Rule Symbol v -> Bool
isFixApplication rl =
  case definedSymbol rl of {Fix{} -> True; _ -> False}
      

narrowRules :: (Alternative m, Ord v, Enum v) => (NarrowedRule Symbol (Either v v) -> Bool) -> [R.Rule Symbol v] -> m [R.Rule Symbol v]
narrowRules sensible rules = 
  case partitionEithers (map narrowRule rules) of
   (_,[]) -> empty
   (untransformed,transformed) -> pure (untransformed ++ concat transformed)
  where
    sound nr = 
      case narrowSubterm nr of
       T.Fun _ ts -> null (UR.usableRules ts rules)
       _ -> False

    renameRule rl = R.rename f rl
      where
        f = either (\ v -> fromJust (lookup v lvs)) id
        lhs = R.lhs rl
        lvs = foldl insrt [(v,v) | Right v <- T.vars lhs] [v | Left v <- T.vars lhs]
        insrt vs v = (v, head (dropWhile (`elem` map snd vs) [v..])):vs
      
    narrowRule rl = 
      case listToMaybe [ ni | ni <- narrow rl rules, sound ni, sensible ni ] of
       Nothing -> Left rl
       Just ni -> Right [renameRule (narrowing n) | n <- narrowings ni]

usableRules :: (Alternative m, Ord v) => [R.Rule Symbol v] -> m [R.Rule Symbol v]
usableRules rs = pure (UR.usableRules [ t | t@(T.Fun Main _) <- RS.lhss rs] rs)

neededRules :: (Alternative m, Ord v) => [R.Rule Symbol v] -> m [R.Rule Symbol v]
neededRules rs = pure (filter needed rs)
  where
    needed rl =
      case definedSymbol rl of
       l@Lambda {} -> l `elem` createdFuns
       l@Fix {} -> l `elem` createdFuns           
       _ -> True
    createdFuns = foldr T.funsDL [] (RS.rhss rs)


try :: (Monad m, Alternative m) => (a -> m a) -> a -> m a
try m a = m a <|> return a

repeated :: (Monad m, Alternative m) => Int -> (a -> m a) -> a -> m a
repeated n m
  | n <= 0 = return
  | otherwise = try (\ a -> m a >>= repeated (n-1) m)


simplifyRules :: (Monad m, Ord v, Enum v, Alternative m) => Int -> [R.Rule Symbol v] -> m [R.Rule Symbol v]
simplifyRules numTimes rules
  | numTimes <= 0 = return rules
  | otherwise =
      try (narrowWith fixPoint) rules
      >>= repeated (numTimes - 1) (narrowWith betaOrCase)
  where
    narrowWith sel rs' = narrowRules sel rs' >>= usableRules >>= neededRules
    
    betaOrCase nr =
          all (\ n -> isCaseRule (narrowedWith n) || isLambdaApplication (narrowedWith n))
          (narrowings nr)
    fixPoint nr =
      all (\ n -> isFixApplication (narrowedWith n)) (narrowings nr)
      
simplify :: Maybe Int -> Problem -> Problem
simplify repeats prob =
  prob { P.rules = P.RulesPair { P.strictRules = simplifiedTrs
                               , P.weakRules = []}
       , P.variables = nub (RS.vars simplifiedTrs)
       , P.symbols = nub (RS.funs simplifiedTrs) }
  where
    numTimes = maybe 15 (max 0) repeats
    simplifiedTrs = fromJust (simplifyRules numTimes (P.allRules (P.rules prob)))
