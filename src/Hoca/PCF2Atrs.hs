-- |  

module Hoca.PCF2Atrs (
  Symbol (..)
  , Var
  , Term
  , Rule
  , Problem
  , toProblem
  ) where

import           Control.Applicative ((<$>),(<*>), Applicative)
import           Control.Monad.RWS
import qualified Control.Monad.State.Lazy as State
import           Data.List (sort)
import qualified Data.Map as Map
import           Data.Maybe (fromJust)
import qualified Data.Set as Set

import qualified Data.Rewriting.Applicative.Rule as R
import           Data.Rewriting.Applicative.Term (app, fun, var)
import qualified Data.Rewriting.Applicative.Term as T
import qualified Data.Rewriting.Term as Term


import           Hoca.Utils (nubRules)
import qualified Hoca.PCF.Core as PCF
import           Hoca.PCF.Sugar.Types (Context (..), Variable (..), ProgramPoint (..))
import           Hoca.Problem (Name(..), Symbol (..), Lbl(..))
import qualified Hoca.Problem as Problem


type Var = Int
type Rule = R.ARule Symbol Var
type Term = T.ATerm Symbol Var
type Problem = Problem.Problem Symbol Var

(-->) :: T.ATerm f v -> T.ATerm f v -> R.ARule f v
(-->) = R.rule

toProblem :: PCF.Exp Context -> Problem
toProblem e = Problem.fromRules (toTRS e)

label :: PCF.Exp Context -> PCF.Exp Name
label expr = State.evalState (labelM expr) (Map.empty,[])
  where
    labelM e@(PCF.Var _ v) = 
        PCF.Var <$> name e <*> return v
    labelM e@(PCF.Con _ g es) = 
        PCF.Con <$> name e <*> return g <*> mapM labelM es
    labelM e@(PCF.Bot _) = 
        PCF.Bot <$> name e
    labelM e@(PCF.App _ e1 e2) = 
        PCF.App <$> name e <*> labelM e1 <*> labelM e2
    labelM e@(PCF.Cond _ e1 cs) =
        PCF.Cond <$> name e
                 <*> labelM e1
                 <*> mapM (\ (g,eg) -> (,) g <$> labelM eg) cs
    labelM e@(PCF.Abs _ v e1) = 
        PCF.Abs <$> name e <*> return v <*> labelM e1
    labelM e@(PCF.Fix _ i es) = 
        PCF.Fix <$> name e <*> return i <*> mapM labelM es

    -- mapping of expressions could be expensive; better use positions e.g.
    name e = do
      m <- fst <$> State.get
      case Map.lookup e m of
       Just l -> return l
       Nothing -> do
         l <- maybeFresh (name' e)
         State.modify (\ (_,seen) -> (Map.insert e l m, seen))
         return l
         
      where 
        name' (PCF.Cond (Context ctx) _ _) = fromTopLetFrame ctx `mappend` Name [LString "cond"]
        name' (PCF.Abs (Context ctx) _ _) = fromTopLetFrame ctx
        name' _ = mempty

        fromTopLetFrame (LetBdy fn vs _: _)  = Name [LString v | Variable v <- vs ++ [fn]]
        fromTopLetFrame (LetRecBdy (Variable fn) _ _: _) = Name [LString "fix", LString fn]
        fromTopLetFrame (_:ctx) = fromTopLetFrame ctx
        fromTopLetFrame _ = Name [LString "main"]
        
    maybeFresh (Name []) = maybeFresh (Name [LInt 1])
    maybeFresh l = do 
      seen <- snd <$> State.get
      let v = head (dropWhile (`elem` seen) (iterate inc l))
      State.modify (\ (es,_) -> (es,v:seen))
      return v
        where 
          inc (Name (LInt i : ls)) = Name (LInt (i+1) : ls)
          inc (Name vs) = Name (LInt 1 : vs)

-- transformation ----------------------------------------------------------------------
      
newtype TM a = TM { execute :: RWS [Int] [Rule] ([Name],Int) a }
             deriving (Applicative, Functor, Monad
                      , MonadReader [Int]
                      , MonadWriter [Rule]
                      , MonadState ([Name],Int))

eval :: TM a -> (a, [Rule])
eval m = evalRWS (execute m) [] ([],0)

freshVars :: TM [Int]
freshVars = fv <$> ask
  where
    fv [] = [0..]
    fv (v:_) = [v+1..]

withVar :: TM r -> TM (Term, r)
withVar m = do
  v <- head <$> freshVars
  r <- local (\vs' -> v : vs') m
  return (var v, r)

withVars :: Int -> TM r -> TM ([Term], r)
withVars n m = do
  vs <- take n <$> freshVars
  r <- local (\vs' -> reverse vs ++ vs') m
  return (map var vs, r)

variable :: Int -> TM Term
variable i = do
  vs <- ask
  return (var (vs!!i))

freshInt :: TM Int
freshInt = do
  (ns,i) <- State.get
  State.put (ns,i+1)
  return i

variables :: TM [Term]
variables = reverse <$> map var <$> ask

freeVars :: PCF.Exp a -> TM (Set.Set Term)
freeVars (PCF.Var _ i) = Set.singleton <$> variable i
freeVars (PCF.Abs _ _ f) = uncurry Set.delete <$> withVar (freeVars f)
freeVars (PCF.App _ e1 e2) =
  Set.union <$> freeVars e1 <*> freeVars e2
freeVars (PCF.Con _ _ es) =
  foldM (\ vs e -> Set.union vs <$> freeVars e) Set.empty es
freeVars (PCF.Bot _) = return Set.empty
freeVars (PCF.Cond _ e cs) = do
  vse <- freeVars e
  foldM (\ vs (_,eg) -> Set.union vs <$> freeVars eg) vse cs
freeVars (PCF.Fix _ _ fs) =
  foldM (\ vs fi -> Set.union vs <$> freeVars fi) Set.empty fs

toTRS :: PCF.Exp Context -> [Rule]
toTRS = nubRules . snd . eval . mainM . label
  where
    cvars = sort . Set.toList
    
    record = tell
    
    mainM (PCF.Abs _ _ f) = void (withVar (mainM f))
    mainM e = do
      t <- toTRSM e
      vs <- variables
      record [fun Main vs --> t ]

    toTRSM (PCF.Var _ i) = variable i
    toTRSM e@(PCF.Abs la _ f) = do
      (v,tf) <- withVar (toTRSM f)
      vs <- freeVars e
      let te = fun (Lambda la) (cvars vs)
      record [ app te v --> tf ]
      return te
    toTRSM (PCF.App _ e1 e2) = app <$> toTRSM e1 <*> toTRSM e2
    toTRSM (PCF.Con _ g es) = fun (Con g) <$> mapM toTRSM es
    toTRSM (PCF.Bot _) = do
      i <- freshInt
      return (fun (Bot i) [])
    
    toTRSM (PCF.Cond l f cs) = do
      vs <- foldM (\ vs' (_,eg) -> Set.union vs' <$> freeVars eg) Set.empty cs
      let cond t = fun (Cond l) (t : cvars vs)
      forM_ cs $ \ (g,eg) -> do
        let ar = PCF.sarity g
        (vsg,tg) <- withVars ar (toTRSM (caseBdy ar eg))
        record [cond (fun (Con g) vsg) --> tg]
      cond <$> toTRSM f
      where
        caseBdy 0 fg = fg
        caseBdy (n+1) (PCF.Abs _ _ fg) = caseBdy n fg
        caseBdy _ _ = error "case expression with invalid body"

    toTRSM e@(PCF.Fix l i fs)
      | 0 <= i && i < length fs
        && all isAbs fs = do
          visited <- elem lf <$> fst <$> get
          vs <- freeVars e
          let te = fun (Fix lf) (cvars vs)
          unless visited $ do
            modify (\ (lfs, j) -> (lf : lfs, j))
            let v = var (maximum (0 : [1 + j | Term.Var j <- Set.toList vs] ))
            tf <- toTRSM (fromJust (foldM PCF.apply f [PCF.Fix l j fs | j <- [0..length fs - 1]]))
            record [ app te v --> app tf v ]
          return te
      where
        isAbs (PCF.Abs {}) = True
        isAbs _ = False
        f@(PCF.Abs lf _ _) = fs!!i
      
    toTRSM (PCF.Fix _ _ _) =
      error "non-lambda abstraction given to fixpoint combinator"



