-- | 

module Hoca.PCF2Atrs (
  Symbol (..)
  , Var
  , Term
  , Rule
  , Problem
  , signature
  , toProblem
  , prettyProblem
  ) where

import           Control.Applicative ((<$>),(<*>), Applicative)
import           Control.Monad.RWS
import qualified Control.Monad.State.Lazy as State
import           Data.List (sort, nub)
import           Data.Maybe (fromJust)
import qualified Data.Rewriting.Problem as P
import qualified Data.Rewriting.Rule as R
import qualified Data.Rewriting.Rules as RS
import qualified Data.Rewriting.Term as T
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import           Hoca.ATRS
import qualified Hoca.PCF as PCF
import qualified Hoca.FP as FP

data Lbl = LString String
         | LInt Int
         deriving (Show, Eq, Ord)
                  
newtype Name = Name [Lbl] deriving (Show, Eq, Ord)

instance PP.Pretty Lbl where
  pretty (LInt i) = PP.int i
  pretty (LString i) = PP.text i

data Symbol =
  Con PCF.Symbol
  | Lambda Name
  | Bot
  | Cond Name
  | Fix Name
  | Main
  deriving (Show, Eq, Ord)

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
type Problem = P.Problem (ASym Symbol) Var

(-->) :: T.Term f v -> T.Term f v -> R.Rule f v
(-->) = R.Rule

prettyProblem :: Problem -> PP.Doc
prettyProblem = P.prettyWST PP.pretty ppVar
    where
      ppVar i = PP.text "x" PP.<> PP.int i

signature :: Problem -> Either String (Signature Symbol)
signature = (fst <$>) . inferTypes . P.allRules . P.rules
  

toProblem :: PCF.Exp FP.Context -> Problem
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
      
newtype TM a = TM { execute :: RWS [Int] [Rule Symbol Var] [Name] a }
             deriving (Applicative, Functor, Monad
                      , MonadReader [Int]
                      , MonadWriter [Rule Symbol Var]
                      , MonadState [Name])

eval :: TM a -> (a, [Rule Symbol Var])
eval m = evalRWS (execute m) [] []

freshVars :: TM [Int]
freshVars = fv <$> ask
  where
    fv [] = [0..]
    fv (v:_) = [v+1..]

withVar :: TM r -> TM (Term Symbol Var, r)
withVar m = do
  v <- head <$> freshVars
  r <- local (\vs' -> v : vs') m
  return (T.Var v, r)

withVars :: Int -> TM r -> TM ([Term Symbol Var], r)
withVars n m = do
  vs <- take n <$> freshVars
  r <- local (\vs' -> reverse vs ++ vs') m
  return (map T.Var vs, r)
  
variable :: Int -> TM (Term Symbol Var)
variable i = do
  vs <- ask
  return (T.Var (vs!!i))

variables :: TM [Term Symbol Var]
variables = reverse <$> map T.Var <$> ask

freeVars :: PCF.Exp a -> TM (Set.Set (Term Symbol Var))
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

toTRS :: PCF.Exp FP.Context -> [Rule Symbol Var]
toTRS = snd . eval . mainM . label
  where
    cvars = sort . Set.toList
    
    mainM (PCF.Abs _ _ f) = void (withVar (mainM f))
    mainM e = do
      t <- toTRSM e
      vs <- variables
      tell [fun Main vs --> t ]

    toTRSM (PCF.Var _ i) = variable i
    toTRSM e@(PCF.Abs _ la f) = do
      (v,tf) <- withVar (toTRSM f)
      vs <- freeVars e
      let te = fun (Lambda la) (cvars vs)
      tell [ app te v --> tf ]
      return te
    toTRSM (PCF.App _ e1 e2) = app <$> toTRSM e1 <*> toTRSM e2
    toTRSM (PCF.Con _ g es) = fun (Con g) <$> mapM toTRSM es
    toTRSM PCF.Bot = return (fun Bot [])
    
    toTRSM (PCF.Cond l f cs) = do
      vs <- foldM (\ vs' (_,eg) -> Set.union vs' <$> freeVars eg) Set.empty cs
      let cond t = fun (Cond l) (t : cvars vs)
      forM_ cs $ \ (g,eg) -> do
        let ar = PCF.sarity g
        (vsg,tg) <- withVars ar (toTRSM (caseBdy ar eg))
        tell [cond (fun (Con g) vsg) --> tg]
      cond <$> toTRSM f
      where
        caseBdy 0 fg = fg
        caseBdy (n+1) (PCF.Abs _ _ fg) = caseBdy n fg
        caseBdy _ _ = error "case expression with invalid body"

    toTRSM e@(PCF.Fix i fs)
      | 0 <= i && i < length fs
        && all isApp fs = do
          visited <- elem lf <$> get
          vs <- freeVars e
          let te = fun (Fix lf) (cvars vs)
          unless visited $ do
            modify (lf :)
            let v = T.Var (maximum (0 : [1 + j | T.Var j <- Set.toList vs] ))
            tf <- toTRSM (fromJust (foldM PCF.apply f [PCF.Fix j fs | j <- [0..length fs - 1]]))
            tell [ app te v --> app tf v ]
          return te
      where
        isApp (PCF.Abs {}) = True
        isApp _ = False
        f@(PCF.Abs _ lf _) = fs!!i
      
    toTRSM (PCF.Fix _ _) =
      error "non-lambda abstraction given to fixpoint combinator"



