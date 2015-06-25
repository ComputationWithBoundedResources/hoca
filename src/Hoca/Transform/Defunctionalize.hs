-- |  

module Hoca.Transform.Defunctionalize (
  -- * Symbols
  Lbl (..)
  , Name (..)
  , Symbol (..)
  , unlabeled
  , isCaseSym,isFixSym,isMainSym,isConstructor  
  --
  , pcfToProblem
  , defunctionalize
  ) where

import           Control.Monad.RWS
import qualified Control.Monad.State.Lazy as State
import           Data.List (sort, nub)
import           Data.Maybe (fromJust)
import qualified Data.Rewriting.Applicative.Rule as R
import           Data.Rewriting.Applicative.Term (app, fun, var)
import qualified Data.Rewriting.Applicative.Term as T
import qualified Data.Set as Set
import           Hoca.Data.MLTypes
import qualified Hoca.PCF.Core as PCF
import           Hoca.PCF.Sugar.Types (Context (..), Variable (..), ProgramPoint (..))
import           Hoca.Problem ((|-))
import qualified Hoca.Problem as P
import           Hoca.Strategy hiding ((>=>))
import qualified Text.PrettyPrint.ANSI.Leijen as PP
-- import Hoca.Utils (tracePretty)


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

type Var = Int
type Problem = P.Problem Symbol Var


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
  pretty (Labeled l s) = PP.pretty s PP.<> PP.text "#" PP.<> PP.int l


unlabeled :: Symbol -> Symbol
unlabeled (Labeled _ s) = unlabeled s
unlabeled s = s

isCaseSym,isFixSym,isMainSym,isConstructor :: Symbol -> Bool
isCaseSym f = case unlabeled f of {Cond{} -> True; _ -> False }
isFixSym f = case unlabeled f of {Fix{} -> True; _ -> False }
isMainSym f = case unlabeled f of {Main{} -> True; _ -> False }
isConstructor f = case unlabeled f of {Con{} -> True; _ -> False }



(-->) :: T.ATerm f v -> T.ATerm f v -> R.ARule f v
(-->) = R.rule

pcfToProblem :: PCF.TypedProgram Context -> Problem
pcfToProblem p = P.fromRules sts (signatureFromList (cdecls ++ fdecls)) (concat defs) where
  (fdecls, defs) = unzip (fromExpression (PCF.expression p))
  cdecls = [ Con (PCF.sname c) ::: td | c ::: td <- signatureToList (PCF.signature p)]
  sts = P.StartTerms { P.defs = [Main]
                     , P.constrs = [c | c ::: _ <- cdecls]}

-- -- transformation ----------------------------------------------------------------------

newtype TM a = TM { execute :: RWS [(Var, Type)] [(TypeDeclaration Symbol, [P.TRule Symbol Var])] ([Symbol],[Name], Int) a }
            deriving (Applicative, Functor, Monad
                      , MonadReader [(Var,Type)] -- the environment
                      , MonadWriter [(TypeDeclaration Symbol, [P.TRule Symbol Var])] -- declarations and associated defining rules generated so far
                      , MonadState ( [Symbol] -- visited fixpoints
                                   , [Name] -- so far used names
                                   , Int    -- fresh integer, for dealing with Bot
                                   ))

-- MA: TODO
eval :: TM a -> (a, [(TypeDeclaration Symbol, [P.TRule Symbol Var])])
eval m = evalRWS (execute m) [] ([],[], 0)

environment :: TM [(Var, Type)]
environment = reverse <$> ask

-- integer supply
freshInt :: TM Int
freshInt = do
  (vs,ns,i) <- State.get
  State.put (vs,ns,i+1)
  return i

-- visited fixed points
visited :: Symbol -> TM Bool
visited n = do 
  (vs,_,_) <- get
  return (n `elem` vs)
  
visit :: Symbol -> TM ()
visit n = modify (\(vs,ns,i) -> (n:vs,ns,i))

-- unique names per expression
makeName :: PCF.TypedExp Context -> TM Name
makeName = maybeFresh . name' where
  name' (PCF.Cond (Context ctx,_) _ _) = fromTopLetFrame ctx `mappend` Name [LString "cond"]
  -- name' (PCF.Abs (Context ctx@(LetBdy{}:_),_) _ _) = fromTopLetFrame ctx
  -- name' (PCF.Abs (Context ctx@(LetRecBdy{}:_),_) _ _) = fromTopLetFrame ctx  
  name' (PCF.Abs (Context ctx,_) _ _) = fromTopLetFrame ctx
  name' _ = mempty

  fromTopLetFrame (LetBdy fn vs _: _)  = Name [LString v | Variable v <- vs ++ [fn]]
  fromTopLetFrame (LetRecBdy (Variable fn) _ _: _) = Name [LString fn]
  fromTopLetFrame (_:ctx) = fromTopLetFrame ctx
  fromTopLetFrame _ = Name [LString "main"]

  inc (Name (LInt i : ls)) = Name (LInt (i+1) : ls)
  inc (Name vs) = Name (LInt 1 : vs)

  maybeFresh (Name []) = maybeFresh (Name [LInt 1])
  maybeFresh l = do 
    (vs,ns,i) <- State.get
    let v = head (dropWhile (`elem` ns) (iterate inc l))
    State.put (vs, v:ns, i)
    return v

-- environments
freshVars :: TM [Var]
freshVars = fv <$> ask
  where
    fv [] = [0..]
    fv ((v,_):_) = [v+1..]

withVar :: Type -> TM r -> TM (Var, r)
withVar tp m = do
  v <- head <$> freshVars
  r <- local (\vs' -> (v, tp) : vs') m
  return (v, r)

-- withVars :: [Type] -> TM r -> TM ([Var], r)
-- withVars tps m = do
--   vs <- zip <$> freshVars <*> return tps
--   r <- local (\vs' -> reverse vs ++ vs') m
--   return (map fst vs, r)

variable :: Int -> TM (Var, Type)
variable i = do
  vs <- ask
  if i >= length vs 
   then error "variable not in scope"
   else return (vs!!i)

        
freeVars :: PCF.TypedExp a -> TM [(Var,Type)]
freeVars f = sort <$> Set.toList <$> fvs f where
  fvs (PCF.Var _ i) = Set.singleton <$> variable i
  fvs (PCF.Abs (_, tp :-> _) _ e) = do 
    (v,tps) <- withVar tp (fvs e)
    return (Set.filter ((/=) v . fst) tps)
  fvs (PCF.App _ e1 e2) =
    Set.union <$> fvs e1 <*> fvs e2
  fvs (PCF.Con _ _ es) =
    foldM (\ vs e -> Set.union vs <$> fvs e) Set.empty es
  fvs (PCF.Bot _) = return Set.empty
  fvs (PCF.Cond _ e cs) = do
    vse <- fvs e
    foldM (\ vs (_,eg) -> Set.union vs <$> fvs eg) vse cs
  fvs (PCF.Fix _ _ fs) =
    foldM (\ vs fi -> Set.union vs <$> fvs fi) Set.empty fs

record :: TypeDeclaration Symbol -> [P.TRule Symbol Var] -> TM ()
record td rs = tell [(td,rs)]

fromExpression :: PCF.TypedExp Context -> [(TypeDeclaration Symbol, [P.TRule Symbol Var])]
fromExpression = snd . eval . (labelM >=> defuncMainM)
 where
    
    name e = (,PCF.typeOf e) <$> makeName e
    
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

    clVars = map (var . fst)
    clTps  = map snd

    defuncMainM (PCF.Abs (_, tp :-> _) _ f) = void (withVar tp (defuncMainM f))
    defuncMainM e = do
      t <- defuncM e
      env <- environment
      let tp = PCF.typeOf e
      record (Main ::: clTps env :~> tp) [ env |- (fun Main (clVars env) --> t, tp)  ]

    defuncM (PCF.Var _ i) = var <$> fst <$> variable i
    defuncM e@(PCF.Abs (nm, tpe@(tin :-> tout)) _ f) = do
      (v,tf) <- withVar tin (defuncM f)
      env <- freeVars e
      let 
        lamSym = Lambda nm
        lamTerm = fun lamSym (clVars env)
      record (lamSym ::: clTps env :~> tpe) [ ((v,tin) : env) |- (app lamTerm (var v) --> tf, tout)]
      return lamTerm
      
    defuncM (PCF.App _ e1 e2) = app <$> defuncM e1 <*> defuncM e2
    defuncM (PCF.Con _ g es) = fun (Con (PCF.sname g)) <$> mapM defuncM es
    defuncM (PCF.Bot (_,tp)) = do
      i <- freshInt
      record (Bot i ::: [] :~> tp) []
      return (fun (Bot i) [])
    
    defuncM (PCF.Cond (nm,tpe) f cs) = do
      envCl <- sort <$> nub <$> concat <$> sequence [ freeVars eg | (_,eg) <- cs ] 
      let 
        condSym = Cond nm
        condTerm t = fun condSym (t : clVars envCl)
      eqs <- forM cs $ \ (g,eg) -> do 
        let 
          condM 0 e' = (,) [] <$> defuncM e'
          condM n (PCF.Abs (_,tp :-> _) _ e') = do 
            (v,(vs,te)) <- withVar tp (condM (n - 1)  e')
            return ((v,tp):vs,te)
          condM _ _ = error "case expression with invalid body"
        (envPat,tg) <- condM (PCF.sarity g) eg
        let 
          con = Con (PCF.sname g)
          pat = fun con (clVars envPat)
        return ((envPat ++ envCl) |- (condTerm pat --> tg, tpe) )
      record (condSym ::: (PCF.typeOf f : clTps envCl) :~> tpe) eqs
      condTerm <$> defuncM f

    defuncM e@(PCF.Fix (_, tpe@(tin :-> tout)) i fs)
      | 0 <= i && i < length fs && all isAbs fs = do          
          env <- freeVars e
          let 
            fixSym = Fix nm
            fixTerm = fun fixSym (clVars env)
          
          visitedB <- visited fixSym
          unless visitedB $ do
            visit fixSym
            let v = maximum (0 : [1 + j | (j,_) <- env] )
            tf <- defuncM (fromJust (foldM PCF.apply f [PCF.Fix (nm,tpe) j fs | j <- [0..length fs - 1]]))
            record (fixSym ::: clTps env :~> tpe) [ ((v,tin) : env) |- (app fixTerm (var v) --> app tf (var v), tout) ]
          return fixTerm
      where
        isAbs (PCF.Abs {}) = True
        isAbs _ = False
        f@(PCF.Abs (nm,_) _ _)
          | i >= length fs = error "fix-point index out of scope"
          | otherwise = fs!!i

    defuncM (PCF.Fix {}) =
      error "non-lambda abstraction given to fixpoint combinator"


defunctionalize ::  PCF.TypedProgram Context :=> P.Problem Symbol Int
defunctionalize = pure . pcfToProblem



