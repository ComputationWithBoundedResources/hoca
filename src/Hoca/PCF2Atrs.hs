-- | 

module Hoca.PCF2Atrs (
  Symbol (..)
  , Term
  , Rule
  , Problem
  , toProblem
  , prettyProblem
  , simplify
  , signature
  , BaseType (..)
  ) where

import           Control.Applicative ((<$>),(<*>), Applicative, Alternative, empty, pure)
import           Control.Monad.RWS
import qualified Control.Monad.State.Lazy as State
import           Data.Either (partitionEithers)
import           Data.List (sort, nub)
import           Data.Maybe (listToMaybe, fromJust)
import qualified Data.MultiSet as MS
import qualified Data.Rewriting.Problem as P
import qualified Data.Rewriting.Rule as R
import qualified Data.Rewriting.Rules as RS
import qualified Data.Rewriting.Term as T
import qualified Data.Set as Set
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import           Hoca.Narrowing
import           Hoca.ATRS
import           Hoca.PCF (Strategy(..))
import qualified Hoca.PCF as PCF
import qualified Hoca.UsableRules as UR

data Lbl = LString String
         | LInt Int
         deriving (Show, Eq, Ord)
                  
type Label = [Lbl]

instance PP.Pretty Lbl where
  pretty (LInt i) = PP.int i
  pretty (LString i) = PP.text i

data Symbol =
  Con PCF.Symbol
  | Lambda (Maybe Label) (PCF.Exp Label)
  | Bot
  | Cond (Maybe Label) (PCF.Exp Label) [(PCF.Symbol, PCF.Exp Label)]
  | Fix (Maybe Label) (PCF.Exp Label)
  | Main
    deriving (Show, Eq, Ord)

ppSym :: PCF.Symbol -> PP.Doc
ppSym = PP.text . PCF.sname

ppCond :: PP.Pretty a => PCF.Exp a -> [(PCF.Symbol, PCF.Exp a)] -> PP.Doc
ppCond e cs =
  ppExp e PP.<> PP.text ";"
  PP.<> PP.hcat [ ppSym g PP.<> PP.text ":" PP.<> ppExp e' <> PP.text ";" | (g,e') <- cs ]

ppExp :: PP.Pretty a => PCF.Exp a -> PP.Doc
ppExp (PCF.Var i) = PP.int i
ppExp (PCF.Con f as) = ppSym f PP.<> PP.brackets (PP.hcat (PP.punctuate (PP.text "*") [ppExp ai | ai <- as]))
ppExp PCF.Bot = PP.text "_|_"
ppExp (PCF.Abs Nothing e) =
  PP.text "L" PP.<> PP.brackets (ppExp e)
ppExp (PCF.Abs (Just l) _) = PP.pretty l
ppExp (PCF.App e1 e2) = PP.brackets (ppExp e1 PP.<> PP.text "." PP.<> ppExp e2)
ppExp (PCF.Fix e) = PP.text "FIX" PP.<> PP.brackets (ppExp e)
ppExp (PCF.Cond Nothing e cs) = PP.text "C" PP.<> PP.brackets (ppCond e cs)
ppExp (PCF.Cond (Just l) _ _) = PP.pretty l

ppLab :: Label -> PP.Doc
ppLab [] = PP.empty
ppLab [l] = PP.pretty l
ppLab (l:ls) = ppLab ls PP.<> PP.text "_" PP.<> PP.pretty l

instance PP.Pretty Symbol where
  pretty (Con g) = ppSym g
  pretty (Lambda Nothing e) = PP.text "L" PP.<> PP.braces (ppExp e)
  pretty (Lambda (Just l) _) = ppLab l
  pretty (Cond Nothing e cs) = PP.text "C" PP.<> PP.braces (ppCond e cs)
  pretty (Cond (Just l) _ _) = ppLab l
  pretty (Fix Nothing e) = PP.text "F" PP.<> PP.braces (ppExp e)
  pretty (Fix (Just l) _) = ppLab l
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
    labelM (PCF.Abs (Just l) e1) = PCF.Abs <$> (Just <$> fresh [LString "Lam", LString l]) <*> labelM e1
    labelM (PCF.App e1 e2) = PCF.App <$> labelM e1 <*> labelM e2
    labelM (PCF.Cond _ e1 cs) =
      PCF.Cond <$> (Just <$> fromLast ([LString "cond"] ++))
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
        inc (LInt i :ls) = LInt (i+1) :ls
        inc vs = LInt 1:vs
        v = head (dropWhile (`elem` seen) (iterate inc l))
      State.put (v:seen)
      return v
      
    fromLast :: (Label -> Label) -> State.State [Label] Label
    fromLast f = do
      seen <- State.get
      fresh (f (head (seen ++ [])))


-- transformation ----------------------------------------------------------------------
      
newtype TM a = TM { execute :: RWS [Int] [Rule Symbol Var] [PCF.Exp Label] a }
             deriving (Applicative, Functor, Monad
                      , MonadReader [Int]
                      , MonadWriter [Rule Symbol Var]
                      , MonadState [PCF.Exp Label])

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

freeVars :: PCF.Exp t -> TM (Set.Set (Term Symbol Var))
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

toTRS :: PCF.Exp String -> [Rule Symbol Var]
toTRS = snd . eval . mainM . betaNormalise . label
  where
    betaNormalise = fromJust . PCF.nf PCF.beta
    cvars = sort . Set.toList
    
    mainM (PCF.Abs _ f) = void (withVar (mainM f))
    mainM e = do
      t <- toTRSM e
      vs <- variables
      tell [fun Main vs --> t ]

    toTRSM (PCF.Var i) = variable i
    toTRSM e@(PCF.Abs l f) = do
      (v,tf) <- withVar (toTRSM f)
      vs <- freeVars e
      let te = fun (Lambda l f) (cvars vs)
      tell [ app te v --> tf ]
      return te
    toTRSM (PCF.App e1 e2) = app <$> toTRSM e1 <*> toTRSM e2
    toTRSM (PCF.Con g es) = fun (Con g) <$> mapM toTRSM es
    toTRSM PCF.Bot = return (fun Bot [])
    
    toTRSM (PCF.Cond l f cs) = do
      vs <- foldM (\ vs' (_,eg) -> Set.union vs' <$> freeVars eg) Set.empty cs
      let cond t = fun (Cond l f cs) (t : cvars vs)
      forM_ cs $ \ (g,eg) -> do
        let ar = PCF.sarity g
        (vsg,tg) <- withVars ar (toTRSM (caseBdy ar eg))
        tell [cond (fun (Con g) vsg) --> tg]
      cond <$> toTRSM f
      where
        caseBdy 0 fg = fg
        caseBdy (n+1) (PCF.Abs _ fg) = caseBdy n fg
        caseBdy _ _ = error "case expression with invalid body"

    toTRSM e@(PCF.Fix f@(PCF.Abs l b)) = do 
      visited <- elem e <$> get
      vs <- freeVars e
      let te = fun (Fix l b) (cvars vs)
      unless visited $ do
        modify (e :)
        (v,tf) <- withVar (toTRSM (fromJust (PCF.beta (PCF.App f e))))
        tell [ app te v --> app tf v ]
      return te

    -- MA: free variable not properly allocated
    -- toTRSM (PCF.Fix (PCF.Abs l b)) = do
    --   (v@(T.Var i),tb) <- withVar (toTRSM b)
    --   vs <- Set.delete v <$> freeVars b
    --   let
    --     te = fun (Fix l b) (cvars vs)
    --     subst = ST.fromMap (Map.singleton i te)
    --   tell [ app te v --> app (S.apply subst tb) v ]
    --   return te
      
    toTRSM (PCF.Fix _) =
      error "non-lambda abstraction given to fixpoint combinator"

    
-- simplification ---------------------------------------------------------------------

isCaseRule :: Rule Symbol v -> Bool
isCaseRule (headSymbol . R.lhs -> Just Cond {}) = True
isCaseRule _ = False

-- isLambdaApplication :: Rule Symbol v -> Bool
-- isLambdaApplication (headSymbol . R.lhs -> Just Lambda {}) = True
-- isLambdaApplication _ = False

isFixApplication :: Rule Symbol v -> Bool
isFixApplication (headSymbol . R.lhs -> Just Fix {}) = True
isFixApplication _ = False
      

narrowRules :: (Alternative m, Ord v, Enum v) => (NarrowedRule (ASym Symbol) (Either v v) -> Bool) -> [Rule Symbol v] -> m [Rule Symbol v]
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

usableRules :: (Alternative m, Ord v) => [Rule Symbol v] -> m [Rule Symbol v]
usableRules rs = pure (UR.usableRules [ t | t@(T.Fun (Sym Main) _) <- RS.lhss rs] rs)

narrowedUsableRules :: (Alternative m) => Int -> [Rule Symbol Var] -> m [Rule Symbol Var]
narrowedUsableRules maxTimes rs = 
  case inferTypes rs of
   Left _ -> empty
   Right (_,ers) -> maybe empty (pure . unTypeRules) (UR.narrowedUsableRules maxTimes stt rst)
     where
       rst = map fst ers
       stt = [ t | t@(T.Fun (Sym Main,_) _) <- RS.lhss rst]       


neededRules :: (Alternative m, Ord v) => [Rule Symbol v] -> m [Rule Symbol v]
neededRules rs = pure (filter needed rs)
  where
    needed rl =
      case headSymbol (R.lhs rl) of
       Just (l@Lambda {}) -> l `elem` createdFuns
       Just (l@Fix {}) -> l `elem` createdFuns           
       _ -> True
    createdFuns = foldr funsDL [] (RS.rhss rs)


try :: (Strategy m) => (a -> m a) -> a -> m a
try m a = m a <||> return a

repeated :: (Strategy m) => Int -> (a -> m a) -> a -> m a
repeated n m
  | n <= 0 = return
  | otherwise = try (m >=> repeated (n-1) m)

exhaustive :: Strategy m => (a -> m a) -> a -> m a
exhaustive rel = try (rel >=> exhaustive rel) 

simplifyRules :: (Strategy m) => Int -> [Rule Symbol Var] -> m [Rule Symbol Var]
simplifyRules nt =
  narrowedUsableRules 1000
  >=> exhaustive (narrowWith caseRule)
  >=> exhaustive (narrowWith fixPointRule)
  >=> repeated nt (\rs -> narrowWith (nonRecRule rs) rs)

  where
    narrowWith sel = narrowRules sel >=> usableRules >=> neededRules
    caseRule nr = all (isCaseRule . narrowedWith) (narrowings nr)
    fixPointRule nr = all (isFixApplication . narrowedWith) (narrowings nr)
    nonRecRule rs nr = all (isNonRec . narrowedWith) (narrowings nr)
      where isNonRec rl = not (any (R.isVariantOf rl) (UR.usableRules [R.rhs rl] rs)) -- FIX type of
    -- betaRule nr = all (\ n -> isLambdaApplication (narrowedWith n)) (narrowings nr)            
    -- simpleRule nr = all (\ n -> isSimpleRule (narrowedWith n)) (narrowings nr)
    --   where
    --     isSimpleRule rl = not (any isApp (T.funs (R.rhs rl)))
    --       where isApp App{} = True
    --             isApp _ = False
    -- nonRec rs nr =
    --   not ((any (R.isVariantOf (narrowedRule nr))) (UR.usableRules [ R.rhs (narrowedWith n) | n <- narrowings nr ] rs)  )
      
simplify :: Maybe Int -> Problem -> Maybe Problem
simplify repeats prob = do
  rs <- simplifyRules numTimes (P.allRules (P.rules prob))
  return prob { P.rules = P.RulesPair { P.strictRules = rs
                                      , P.weakRules = []}
              , P.variables = nub (RS.vars rs)
              , P.symbols = nub (RS.funs rs) }
  where
    numTimes = maybe 15 (max 0) repeats


data BaseType = BaseType deriving (Eq, Ord, Show)

instance PP.Pretty BaseType where
  pretty BaseType = PP.text "*"

signature :: Problem -> Either String (Signature Symbol)
signature = (fst <$>) . inferTypes . P.allRules . P.rules
  
