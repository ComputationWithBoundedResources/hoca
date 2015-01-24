#!/usr/local/bin/runhaskell
module Main where
import Prelude hiding ((&&),(||), not)
import qualified Prelude as Prelude
import           Control.Applicative ((<$>))
import           Control.Monad (foldM)
import qualified Hoca.FP as FP
import qualified Hoca.PCF as PCF
import qualified Hoca.Narrowing as N
import qualified Hoca.Problem as Problem
import qualified Hoca.ATRS as ATRS
import           Hoca.Utils (putDocLn, writeDocFile, render)
import           Hoca.Transform
import           System.Environment (getArgs)
import           System.IO (hPutStrLn, stderr)
import GHC.IO (unsafePerformIO)
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Data.Maybe (fromJust)
import qualified Data.Rewriting.Rule as R
import qualified Data.Rewriting.Term as T
import System.Exit (exitSuccess,exitFailure)

type Problem = Problem.Problem Problem.Symbol Int
type Rule = ATRS.Rule Problem.Symbol Int


class Boolean a where
  (&&) :: a -> a -> a
  (||) :: a -> a -> a  
  not :: a -> a
  
infixr 3 &&
infixr 2 ||

instance Boolean Bool where
  (&&) = (Prelude.&&)
  (||) = (Prelude.||)
  not = Prelude.not

instance Boolean b => Boolean (a -> b) where
  f && g = \ a -> (f a && g a)
  f || g = \ a -> (f a || g a)  
  not f = \ a -> not (f a)

expressionFromArgs :: FilePath -> [String] -> IO (PCF.Exp FP.Context)
expressionFromArgs fname args = do
  r <- mk <$> readFile fname
  case r of
   Left e -> putErrLn e >> exitFailure
   Right pcf -> return pcf
  where
    mk s = do
      fun <- fromString fname s
      foldM (\ p (i,si) -> PCF.App [] p <$> fromString ("argument " ++ show i) si)
        fun (zip [(1::Int)..] args)
    fromString src str = FP.expFromString src str >>= FP.toPCF

cfa :: PCF.Strategy m => Problem -> m Problem
cfa = dfaInstantiate hoHeadVariables
  where
    hoHeadVariables (trl,_) =
      case R.rhs trl of
       T.Var (v, _ ATRS.:~> _) -> [v]
       _ -> ATRS.headVars (R.rhs (ATRS.unTypeRule trl))

dfa :: PCF.Strategy m => Problem -> m Problem
dfa = dfaInstantiate (R.vars . ATRS.unTypeRule . fst)       
--    allVars = map fst . R.vars

anyRule, caseRule, lambdaRule, fixRule, recursiveRule :: Problem -> Rule -> Bool
caseRule _ rl =
  case Problem.unlabeled <$> ATRS.headSymbol (R.lhs rl) of
   Just Problem.Cond {} -> True
   _ -> False
lambdaRule _ rl = 
  case Problem.unlabeled <$> ATRS.headSymbol (R.lhs rl) of
   Just Problem.Lambda {} -> True
   _ -> False
fixRule _ rl = 
  case Problem.unlabeled <$> ATRS.headSymbol (R.lhs rl) of
   Just Problem.Fix {} -> True
   _ -> False
anyRule _ _ = True  
recursiveRule p = Problem.isRecursive p

definingRule :: String -> Problem -> Rule -> Bool
definingRule name _ rl =
  case ATRS.headSymbol (R.lhs rl) of
   Just f -> render f == name
   _ -> False

-- nonRecursiveNarrowing :: Problem -> N.NarrowedRule (ATRS.ASym Problem.Symbol) Int Int -> Bool
-- nonRecursiveNarrowing _ n = 

withRule :: (Problem -> Rule -> Bool) -> Problem -> N.NarrowedRule (ATRS.ASym Problem.Symbol) Int Int -> Bool
withRule p rs = all (p rs) . map N.narrowedWith . N.narrowings

onRule :: (Problem -> Rule -> Bool) -> Problem -> N.NarrowedRule (ATRS.ASym Problem.Symbol) Int Int -> Bool
onRule p rs = p rs . N.narrowedRule

n1 :: PCF.Strategy m => Problem -> m Problem
n1 = exhaustive ((narrow (withRule caseRule) >=> traceProblem "case narrowing")
                 <=> (rewrite (withRule lambdaRule) >=> traceProblem "lambda rewrite"))
     >=> exhaustive (rewrite (withRule fixRule) >=> traceProblem "fix rewrite")
     >=> try usableRules >=> try neededRules          
     >=> exhaustive (narrow (withRule (not recursiveRule)) >=> traceProblem "non-recursive narrowing")
     >=> try usableRules >=> try neededRules

nonRecursive :: N.NarrowedRule (ATRS.ASym Problem.Symbol) Int Int -> Bool
nonRecursive = undefined

  
simplify :: PCF.Strategy m => Problem -> m Problem
simplify =
  traceProblem "initial"
  >=> try (cfa >=> traceProblem "CFA")
  >=> exhaustive ((narrow (withRule caseRule) >=> traceProblem "case narrowing")
                  <=> (rewrite (withRule lambdaRule) >=> traceProblem "lambda rewrite"))
  >=> exhaustive (rewrite (withRule fixRule) >=> traceProblem "fix rewrite")
  >=> try usableRules >=> try neededRules          
  >=> exhaustive (narrow (withRule (not recursiveRule)) >=> traceProblem "non-recursive narrowing")
  >=> try usableRules >=> try neededRules
  >=> try (uncurryRules >=> try usableRules >=> try neededRules >=> traceProblem "uncurried")
  >=> exhaustive (narrow (withRule (not recursiveRule)) >=> traceProblem "non-recursive narrowing")
  >=> try usableRules >=> try neededRules  

narrowConst :: PCF.Strategy m => Problem -> m Problem
narrowConst =
  narrow (\ _ ns -> all (decreasingConst (N.narrowSubterm ns) . N.narrowing) (N.narrowings ns))
  >=> try usableRules >=> try neededRules
  where
    decreasingConst t (R.Rule _ r) =
      T.isGround t
      || (not (null as) && all (any (\ (li,ri) -> isConstantTerm li && isConstantTerm ri && size li > size ri)) as)
      where
        as = [ zip (ATRS.args t) (ATRS.args ri)
             | ri <- T.subterms r, ATRS.headSymbol t == ATRS.headSymbol ri ]
    -- decreasingConst t@(T.Fun f ts) (R.Rule l r) = T.isGround t 
      -- null as || all (any (\ (li,ri) -> isConstantTerm li && isConstantTerm ri && size li > size ri)) as where
      --   as = [ zip ts rs
      --        | T.Fun g rs <- T.subterms r, f == g ]

    isConstantTerm t = T.isGround t && all isConstructor (ATRS.funs t) where 
      isConstructor Problem.Con{} = True
      isConstructor _ = False

    size = T.fold (const (1::Int)) (const (succ . sum))
--     -- T.Var {} `embeds` _ = False
--     -- s@(T.Fun f ss) `embeds` t@(T.Fun g ts) =
--     --   t `elem` (T.properSubterms s)
--     --   || (f == g && 



-- Interactive

newtype ST = ST (Maybe Problem)

instance PP.Pretty ST where
  pretty (ST Nothing) = PP.text "No problem loaded"
  pretty (ST (Just p)) = PP.pretty p
    
data STATE = STATE ST [ST] 

curState :: STATE -> ST
curState (STATE st _) = st

stateRef :: IORef STATE
stateRef = unsafePerformIO $ newIORef (STATE (ST Nothing) [])
{-# NOINLINE stateRef #-}

putState :: ST -> IO ()
putState st = do
  STATE cur hst <- readIORef stateRef
  let hst' =
        case cur of
         ST Just {} -> cur : hst
         _ -> hst 
  writeIORef stateRef (STATE st hst')

getState :: IO ST
getState = curState <$> readIORef stateRef

printState :: IO ()
printState = getState >>= putDocLn

modifyState :: (ST -> ST) -> IO ()
modifyState f = do
  st <- getState
  putState (f st)

load' :: FilePath -> IO ()
load' fn = do
  pcfToTrs <$> expressionFromArgs fn []
  >>= maybe (putDocLn "Loading of problem failed.") (putState . ST . Just)

load :: FilePath -> IO ()
load fn = load' fn >> printState

withProblemM :: (Problem -> IO a) -> IO a
withProblemM f = do
  ST mp <- getState
  maybe (error "no problem loaded") f mp

withProblem :: (Problem -> a) -> IO a
withProblem f = withProblemM (return . f)

select :: (Problem -> Rule -> Bool) -> IO [Rule]
select f = withProblemM sel where
  sel p  = do
    let rs = [ e | e@(_,rl) <- Problem.rulesEnum p, f p rl]
    putDocLn (Problem.restrictIdx (map fst rs) p)
    putDocLn PP.empty
    return (map snd rs)

save :: FilePath -> IO ()
save fn = withProblemM (writeDocFile fn . Problem.prettyWST)

state :: IO ()
state = printState             

reset :: IO ()
reset = do 
  STATE h hst <- readIORef stateRef
  putState (last (h:hst))
  printState
  
undo' :: IO Bool
undo' = do
  STATE _ hst <- readIORef stateRef 
  case hst of 
   [] -> return False
   (h:hs) -> do 
     writeIORef stateRef (STATE h hs)
     return True

undo :: IO ()
undo = do undone <- undo' 
          if undone 
            then printState
            else putDocLn (PP.text "Nothing to undo")

apply :: (Problem -> Maybe Problem) -> IO ()
apply m = do 
  ST st <- getState  
  case st of
   Nothing ->
     putDocLn (PP.vcat [ PP.text "No system loaded."
                       , PP.text ""
                       , PP.text "Use 'load <filename>' to load a new problem."])
   Just p ->
     case m p of
      Nothing -> putDocLn "Transformation inapplicable."
      r -> putState (ST r) >> printState


-- Main
    
helpMsg :: String
helpMsg = "pcf2trs [--eval|--pcf|--no-simp] <file> [args]*"

putErrLn :: String -> IO ()
putErrLn = hPutStrLn stderr

main :: IO ()
main = do
  args <- getArgs  
  case args of
   "--help" : _ -> putStrLn helpMsg
   "--eval" : fname : as -> do
     e <- expressionFromArgs fname as
     putDocLn (PP.pretty (fromJust (PCF.nf PCF.cbv e)))
   "--pcf" : fname : as -> do
     e <- expressionFromArgs fname as
     putDocLn (PP.pretty e)
     -- putDocLn (PP.pretty (fromJust (PCF.nf (PCF.ctxtClosure PCF.beta) e)))
   "--no-simp" : fname : as -> 
     transform False fname as
   fname : as ->
     transform True fname as     
   _ -> error helpMsg
  exitSuccess
  where
    transform doSimp fname as = do
      e <- expressionFromArgs fname as  
      case tr e of
       Just prob -> putDocLn (Problem.prettyWST prob)
       Nothing -> do
         putErrLn "the program cannot be transformed"
         exitFailure
      where
        tr | doSimp = pcfToTrs >=> simplify
           | otherwise = pcfToTrs




-- rulesFromFile fname = do
--   
