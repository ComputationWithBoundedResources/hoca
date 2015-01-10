#!/usr/local/bin/runhaskell
module Main where
import           Control.Applicative ((<$>))
import           Control.Monad (foldM)
import qualified Hoca.FP as FP
import qualified Hoca.PCF as PCF
import qualified Hoca.Narrowing as N
import qualified Hoca.Problem as Problem
import qualified Hoca.ATRS as ATRS
import           Hoca.Utils (putDocLn, writeDocFile)
import           Hoca.Transform
import           System.Environment (getArgs)
import           System.IO (hPutStrLn, stderr)
import GHC.IO (unsafePerformIO)
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import Control.Monad (liftM)
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Data.Maybe (fromJust)
import qualified Data.Rewriting.Rule as R
import qualified Data.Rewriting.Term as T
import System.Exit (exitSuccess,exitFailure)

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


dfa :: PCF.Strategy m => Problem -> m Problem
dfa = dfaInstantiate hoHeadVariables
  where
    hoHeadVariables (trl,_) =
      case R.rhs trl of
       T.Var (v, _ ATRS.:~> _) -> [v]
       _ -> ATRS.headVars (R.rhs (ATRS.unTypeRule trl))
    allVars = map fst . R.vars


narrowWith :: PCF.Strategy m => (Problem -> Rule -> Bool) -> Problem -> m Problem
narrowWith f =
  narrow (\ p -> all (f p) . map N.narrowedWith . N.narrowings)
  >=> try usableRules >=> try neededRules

rewriteWith :: PCF.Strategy m => (Problem -> Rule -> Bool) -> Problem -> m Problem
rewriteWith p =
  rewrite (\ rs -> all (p rs) . map N.narrowedWith . N.narrowings)
  >=> try usableRules >=> try neededRules

anyRules, caseRules,lambdaRules,fixRules,nonRecursiveRules :: Problem -> Rule -> Bool
caseRules _ rl =
  case ATRS.headSymbol (R.lhs rl) of
   Just Cond {} -> True
   _ -> False
lambdaRules _ rl = 
  case ATRS.headSymbol (R.lhs rl) of
   Just Lambda {} -> True
   _ -> False
fixRules _ rl = 
  case ATRS.headSymbol (R.lhs rl) of
   Just Fix {} -> True
   _ -> False
anyRules _ _ = True  
nonRecursiveRules p = not . Problem.isRecursive p
--inlining p rl = 

simplify :: Problem -> Maybe Problem
simplify =
  traceProblem "initial"
  >=> try usableRules >=> try neededRules >=> traceProblem "usable"
  >=> exhaustive (narrowWith caseRules >=> traceProblem "case narrowing")
  >=> exhaustive (rewriteWith lambdaRules >=> traceProblem "lambda rewrite")
  >=> exhaustive (rewriteWith fixRules >=> traceProblem "fix rewrite")
  >=> try (dfa >=> traceProblem "instantiation")
  -- >=> exhaustive (narrowConst >=> traceProblem "constant narrowing")
  -- >=> exhaustive (narrowWith (\ _ _ ->  True))
  >=> exhaustive ((narrowWith caseRules >=> traceProblem "case narrowing")
                  -- <=> (narrowConst >=> traceProblem "constant narrowing")
                   <=> (narrowWith nonRecursiveRules >=> traceProblem "non-recursive narrowing"))

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
      isConstructor Con{} = True
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

withProblem :: (Problem -> IO a) -> IO a
withProblem f = do
  ST mp <- getState
  maybe (error "no problem loaded") f mp

save :: FilePath -> IO ()
save fn = withProblem (writeDocFile fn . Problem.prettyWST)

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
     putDocLn (PP.pretty (fromJust (PCF.nf (PCF.ctxtClosure PCF.beta) e)))
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
