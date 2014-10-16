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
import           Control.Monad.RWS
import qualified Data.Set as Set
import           Data.List (sort, nub)
import           Data.Either (partitionEithers)
import           Data.Maybe (listToMaybe, fromJust)
import qualified Data.Map as Map
import qualified Data.MultiSet as MS
import qualified Data.Rewriting.Problem as P
import qualified Data.Rewriting.Rule as R
import qualified Data.Rewriting.Rules as RS
import qualified Data.Rewriting.Substitution as S
import qualified Data.Rewriting.Substitution.Type as ST
import qualified Data.Rewriting.Term as T
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           Control.Applicative (Applicative)
import           Hoca.Narrowing
import           Hoca.PCF (Strategy(..))
import qualified Hoca.PCF as PCF
import qualified Hoca.UsableRules as UR


data Lbl = LString String
         | LInt Int
         deriving (Show, Eq, Ord)
                  
type Label = [Lbl]

data Symbol =
  Con PCF.Symbol
  | Lambda (Maybe Label) (PCF.Exp Label)
  | Bot
  | App
  | Cond (Maybe Label) (PCF.Exp Label) [(PCF.Symbol, PCF.Exp Label)]
  | Fix (Maybe Label) (PCF.Exp Label)
  | Main
    deriving (Show, Eq, Ord)


instance PP.Pretty Lbl where
  pretty (LInt i) = PP.int i
  pretty (LString i) = PP.text i

type Var = Int
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
      ppFun (Cond Nothing e cs) = PP.text "C" PP.<> PP.braces (ppCond e cs)
      ppFun (Cond (Just l) _ _) = ppLab l
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
      ppExp (PCF.Abs Nothing e) =
        PP.text "L" PP.<> PP.brackets (ppExp e)
      ppExp (PCF.Abs (Just l) _) = PP.pretty l
      ppExp (PCF.App e1 e2) =
        PP.brackets (ppExp e1 PP.<> PP.text "." PP.<> ppExp e2)
      ppExp (PCF.Fix e) = PP.text "FIX" PP.<> PP.brackets (ppExp e)
      ppExp (PCF.Cond Nothing e cs) = PP.text "C" PP.<> PP.brackets (ppCond e cs)
      ppExp (PCF.Cond (Just l) _ _) = PP.pretty l

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
    labelM (PCF.Cond _ e1 cs) =
      PCF.Cond <$> (Just <$> fromLast (++ [LString "cond"]))
               <*> labelM e1
               <*> mapM (\ (g,eg) -> (,) g <$> labelM eg) cs
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
    fromLast :: (Label -> Label) -> State.State [Label] Label
    fromLast f = do
      seen <- State.get
      fresh (f (head (seen ++ [])))
      
-- flattenExp :: PCF.Exp e -> (PCF.Exp e, [PCF.Exp e])
-- flattenExp (PCF.App e1 e2) =
--   case flattenExp e1 of (e11,es) -> (e11,es++[e2])
-- flattenExp e = (e,[])

newtype TM a = TM { execute :: RWS [Int] [Rule] [PCF.Exp Label] a }
             deriving (Applicative, Functor, Monad
                      , MonadReader [Int]
                      , MonadWriter [Rule]
                      , MonadState [PCF.Exp Label])

eval :: TM a -> (a, [Rule])
eval m = evalRWS (execute m) [] []

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

variables :: TM [Term]
variables = reverse <$> map T.Var <$> ask

toTRS :: PCF.Exp String -> [Rule]
toTRS = snd . eval . mainM . label
  where
    cvars = sort . Set.toList

    mainM (PCF.Abs _ f) = void (withVar (mainM f))
    mainM e = do
      t <- toTRSM e
      vs <- variables
      tell [T.Fun Main vs --> t ]

    freeVars (PCF.Var i) = Set.singleton <$> variable i
    freeVars (PCF.Abs _ f) = uncurry Set.delete <$> withVar (freeVars f)
    freeVars (PCF.App e1 e2) =
      Set.union <$> freeVars e1 <*> freeVars e2
    freeVars (PCF.Con _ es) =
      foldM (\ vs e -> Set.union vs <$> freeVars e) Set.empty es
    freeVars PCF.Bot = return Set.empty
    freeVars (PCF.Cond _ e cs) = do
      vse <- freeVars e
      foldM (\ vs (_,eg) -> Set.union vs <$> freeVars eg) vse cs
    freeVars (PCF.Fix f) = freeVars f
      
    toTRSM (PCF.Var i) = variable i
    toTRSM e@(PCF.Abs l f) = do
      (v,tf) <- withVar (toTRSM f)
      vs <- freeVars e
      let te = T.Fun (Lambda l f) (cvars vs)
      tell [ app te v --> tf ]
      return te
    toTRSM (PCF.App e1 e2) = app <$> toTRSM e1 <*> toTRSM e2
    toTRSM (PCF.Con g es) = T.Fun (Con g) <$> mapM toTRSM es
    toTRSM PCF.Bot = return (T.Fun Bot [])
    
    toTRSM (PCF.Cond l f cs) = do
      vs <- foldM (\ vs' (_,eg) -> Set.union vs' <$> freeVars eg) Set.empty cs
      let cond t = T.Fun (Cond l f cs) (t : cvars vs)
      forM_ cs $ \ (g,eg) -> do
        let ar = PCF.sarity g
        (vsg,tg) <- withVars ar (toTRSM (caseBdy ar eg))
        tell [cond (T.Fun (Con g) vsg) --> tg]
      cond <$> toTRSM f
      where
        caseBdy 0 fg = fg
        caseBdy (n+1) (PCF.Abs _ fg) = caseBdy n fg
        caseBdy _ _ = error "case expression with invalid body"

    toTRSM e@(PCF.Fix f@(PCF.Abs l b)) = do 
      visited <- elem e <$> get
      vs <- freeVars e
      let te = T.Fun (Fix l b) (cvars vs)
      unless visited $ do
        modify (e :)
        (v,tf) <- withVar (toTRSM (fromJust (PCF.beta (PCF.App f e))))
        tell [ app te v --> app tf v ]
      return te
    --   mr <- 
    --   case mr of
    --    Just r -> return r
    --    Nothing -> do
    --     v <- freshVar
    --     (tb,fvarsb) <- pushVar v (toTRSM (fromJust (PCF.beta (PCF.App f e))))
    --     let
    --       fvars = Set.delete v fvarsb
    --       tf = T.Fun (Fix l b) (cvars fvars)
    --     tell [ app tf (var v) --> app tb (var v) ]
    --     modify (Map.insert e (tf,fvars))
    --     return (tf,fvars)
    toTRSM (PCF.Fix _) =
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
      all (variablePreserving . narrowedWith) (narrowings nr)
      || argumentNormalised (narrowSubterm nr)
      where
        -- redexDeleting rl = varsMS (R.lhs rl) `MS.isProperSubsetOf` varsMS (R.rhs rl)
        --   where varsMS = MS.fromList . T.vars
        variablePreserving rl = varsMS (R.lhs rl) == varsMS (R.rhs rl)
          where varsMS = MS.fromList . T.vars
        argumentNormalised (T.Fun _ ts) = null (UR.usableRules ts rules)
        argumentNormalised _ = True
        
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


try :: (Strategy m) => (a -> m a) -> a -> m a
try m a = m a <||> return a

repeated :: (Strategy m) => Int -> (a -> m a) -> a -> m a
repeated n m
  | n <= 0 = return
  | otherwise = try (m >=> repeated (n-1) m)

exhaustive :: Strategy m => (a -> m a) -> a -> m a
exhaustive rel = try (rel >=> exhaustive rel) 

simplifyRules :: (Strategy m, Ord v, Enum v) => Int -> [R.Rule Symbol v] -> m [R.Rule Symbol v]
simplifyRules nt =
  exhaustive (narrowWith caseRule)
  >=> exhaustive (narrowWith fixPointRule)
  >=> repeated nt (\rs -> narrowWith (nonRecRule rs) rs)

      -- >>= narrowWith fixPointRule
  where
    narrowWith sel = narrowRules sel >=> usableRules >=> neededRules

    caseRule nr = all (\ n -> isCaseRule (narrowedWith n)) (narrowings nr)
    betaRule nr = all (\ n -> isLambdaApplication (narrowedWith n)) (narrowings nr)
    fixPointRule nr = all (\ n -> isFixApplication (narrowedWith n)) (narrowings nr)
    simpleRule nr = all (\ n -> isSimpleRule (narrowedWith n)) (narrowings nr)
      where
        isSimpleRule rl = not (any isApp (T.funs (R.rhs rl)))
          where isApp App{} = True
                isApp _ = False
    nonRecRule rs nr = all (\ n -> isNonRec (narrowedWith n)) (narrowings nr)
      where isNonRec rl = not (any (R.isVariantOf rl) (UR.usableRules [R.rhs rl] rs)) -- FIX type of 

    nonRec rs nr =
      not ((any (R.isVariantOf (narrowedRule nr))) (UR.usableRules [ R.rhs (narrowedWith n) | n <- narrowings nr ] rs)  )

    -- betaOrCase nr =
    --       all (\ n -> isCaseRule (narrowedWith n) || isLambdaApplication (narrowedWith n))
    --       (narrowings nr)
    -- fixPoint nr =
    --   all (\ n -> isFixApplication (narrowedWith n)) (narrowings nr)
      
simplify :: Maybe Int -> Problem -> Problem
simplify repeats prob =
  prob { P.rules = P.RulesPair { P.strictRules = simplifiedTrs
                               , P.weakRules = []}
       , P.variables = nub (RS.vars simplifiedTrs)
       , P.symbols = nub (RS.funs simplifiedTrs) }
  where
    numTimes = maybe 15 (max 0) repeats
    simplifiedTrs = fromJust (simplifyRules numTimes (P.allRules (P.rules prob)))
