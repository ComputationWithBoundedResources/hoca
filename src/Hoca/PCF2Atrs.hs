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
import           Data.Maybe (fromJust)
import qualified Data.Rewriting.Rule as R
import qualified Data.Rewriting.Term as T
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Hoca.ATRS as ATRS
import           Hoca.Utils (nubRules)
import qualified Hoca.PCF as PCF
import qualified Hoca.FP as FP
import Hoca.Problem (Name(..), Symbol (..), Lbl(..))
import qualified Hoca.Problem as Problem


type Var = Int
type Rule = ATRS.Rule Symbol Var
type Term = ATRS.Term Symbol Var
type Problem = Problem.Problem Symbol Var

(-->) :: T.Term f v -> T.Term f v -> R.Rule f v
(-->) = R.Rule

toProblem :: PCF.Exp FP.Context -> Problem
toProblem e = Problem.fromRules (toTRS e)

label :: PCF.Exp FP.Context -> PCF.Exp Name
label expr = State.evalState (labelM expr) (Map.empty,[])
  where
    labelM e@(PCF.Var _ v) = PCF.Var <$> name e <*> return v
    labelM e@(PCF.Con _ g es) = PCF.Con <$> name e <*> return g <*> mapM labelM es
    labelM PCF.Bot = return PCF.Bot
    labelM e@(PCF.App _ e1 e2) = PCF.App <$> name e <*> labelM e1 <*> labelM e2
    labelM e@(PCF.Cond _ e1 cs) =
      PCF.Cond <$> name e
               <*> labelM e1
               <*> mapM (\ (g,eg) -> (,) g <$> labelM eg) cs
    labelM e@(PCF.Abs v _ e1) = PCF.Abs v <$> name e <*> labelM e1
    labelM (PCF.Fix i es) = PCF.Fix i <$> mapM labelM es

    withSurroundingLet ctx n =
      case surroundingLet ctx of
       Nothing -> maybeFresh (Name [n, LString "main"])
       Just l -> maybeFresh (Name [n, LString l])
       where
         surroundingLet [] = Nothing
         surroundingLet (FP.LetBdy fn _ _ : _) = Just fn
         surroundingLet (FP.LetRecBdy fn _ _ : _) = Just fn    
         surroundingLet (_ : ctx') = surroundingLet ctx'

    name e = do
      m <- fst <$> State.get
      case Map.lookup e m of
       Just l -> return l
       Nothing -> do
         l <- name' e
         State.modify (\ (_,seen) -> (Map.insert e l m, seen))
         return l
         
      where 
        name' (PCF.Cond ctx _ _) = withSurroundingLet ctx (LString "cond")
        name' (PCF.Abs _ ctx _) = fromCtx ctx
        name' _ = maybeFresh (Name [])
        fromCtx (FP.LetBdy fn vs _: _) = maybeFresh (Name [LString v | v <- vs ++ [fn]])
        fromCtx (FP.LetRecBdy fn vs _: _) = maybeFresh (Name [LInt (length vs), LString fn])
--        fromCtx (FP.LetIn fn _ : ctx') = LString fn : fromCtx ctx'
        fromCtx (FP.LambdaBdy _ : ctx') = withSurroundingLet ctx' (LString "anonymous")
        fromCtx ctx' = withSurroundingLet ctx' (LInt 0)
    
    maybeFresh :: Name -> State.State (Map.Map (PCF.Exp FP.Context) Name, [Name]) Name
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
  return (T.Var v, r)

withVars :: Int -> TM r -> TM ([Term], r)
withVars n m = do
  vs <- take n <$> freshVars
  r <- local (\vs' -> reverse vs ++ vs') m
  return (map T.Var vs, r)

variable :: Int -> TM Term
variable i = do
  vs <- ask
  return (T.Var (vs!!i))

freshInt :: TM Int
freshInt = do
  (ns,i) <- State.get
  State.put (ns,i+1)
  return i

variables :: TM [Term]
variables = reverse <$> map T.Var <$> ask

freeVars :: PCF.Exp a -> TM (Set.Set Term)
freeVars (PCF.Var _ i) = Set.singleton <$> variable i
freeVars (PCF.Abs _ _ f) = uncurry Set.delete <$> withVar (freeVars f)
freeVars (PCF.App _ e1 e2) =
  Set.union <$> freeVars e1 <*> freeVars e2
freeVars (PCF.Con _ _ es) =
  foldM (\ vs e -> Set.union vs <$> freeVars e) Set.empty es
freeVars PCF.Bot = return Set.empty
freeVars (PCF.Cond _ e cs) = do
  vse <- freeVars e
  foldM (\ vs (_,eg) -> Set.union vs <$> freeVars eg) vse cs
freeVars (PCF.Fix _ fs) =
  foldM (\ vs fi -> Set.union vs <$> freeVars fi) Set.empty fs

toTRS :: PCF.Exp FP.Context -> [Rule]
toTRS = nubRules . snd . eval . mainM . label
  where
    cvars = sort . Set.toList
    
    record = tell
    
    mainM (PCF.Abs _ _ f) = void (withVar (mainM f))
    mainM e = do
      t <- toTRSM e
      vs <- variables
      record [ATRS.fun Main vs --> t ]

    toTRSM (PCF.Var _ i) = variable i
    toTRSM e@(PCF.Abs _ la f) = do
      (v,tf) <- withVar (toTRSM f)
      vs <- freeVars e
      let te = ATRS.fun (Lambda la) (cvars vs)
      record [ ATRS.app te v --> tf ]
      return te
    toTRSM (PCF.App _ e1 e2) = ATRS.app <$> toTRSM e1 <*> toTRSM e2
    toTRSM (PCF.Con _ g es) = ATRS.fun (Con g) <$> mapM toTRSM es
    toTRSM PCF.Bot = do
      -- i <- freshInt
      return (ATRS.fun (Bot 0) [])
    
    toTRSM (PCF.Cond l f cs) = do
      vs <- foldM (\ vs' (_,eg) -> Set.union vs' <$> freeVars eg) Set.empty cs
      let cond t = ATRS.fun (Cond l) (t : cvars vs)
      forM_ cs $ \ (g,eg) -> do
        let ar = PCF.sarity g
        (vsg,tg) <- withVars ar (toTRSM (caseBdy ar eg))
        record [cond (ATRS.fun (Con g) vsg) --> tg]
      cond <$> toTRSM f
      where
        caseBdy 0 fg = fg
        caseBdy (n+1) (PCF.Abs _ _ fg) = caseBdy n fg
        caseBdy _ _ = error "case expression with invalid body"

    toTRSM e@(PCF.Fix i fs)
      | 0 <= i && i < length fs
        && all isApp fs = do
          visited <- elem lf <$> fst <$> get
          vs <- freeVars e
          let te = ATRS.fun (Fix lf) (cvars vs)
          unless visited $ do
            modify (\ (lfs, j) -> (lf : lfs, j))
            let v = T.Var (maximum (0 : [1 + j | T.Var j <- Set.toList vs] ))
            tf <- toTRSM (fromJust (foldM PCF.apply f [PCF.Fix j fs | j <- [0..length fs - 1]]))
            record [ ATRS.app te v --> ATRS.app tf v ]
          return te
      where
        isApp (PCF.Abs {}) = True
        isApp _ = False
        f@(PCF.Abs _ lf _) = fs!!i
      
    toTRSM (PCF.Fix _ _) =
      error "non-lambda abstraction given to fixpoint combinator"



