#!/usr/local/bin/runhaskell

{-# LANGUAGE TypeOperators #-}

module Main where


import qualified Data.GraphViz.Attributes as GVattribs
import qualified Data.GraphViz.Attributes.Colors.SVG as GVSVG
import qualified Data.GraphViz.Attributes.Complete as GVattribsc
import           Data.GraphViz.Commands
import           Data.GraphViz.Types.Generalised (DotGraph)
import qualified Data.GraphViz.Types.Monadic as GV

import qualified Data.Rewriting.Applicative.Rule as R
import           Data.Rewriting.Applicative.SimpleTypes (Type (..))
import qualified Data.Rewriting.Applicative.SimpleTypes as ST
import qualified Data.Rewriting.Applicative.Term as T
import qualified Data.Rewriting.Term as Term

import qualified Prelude
import           Prelude hiding ((&&),(||), not)
import           System.Environment (getArgs)
import           System.Exit (exitSuccess,exitFailure)
import           System.IO (hPutStrLn, stderr)
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import           Data.Graph (flattenSCC, stronglyConnCompR)
import           Data.Monoid (mempty)
import           Control.Monad (foldM, void, forM)
import           Data.IORef (IORef, newIORef, readIORef, writeIORef)
import           Data.List (nub)
import           Data.Either (either)
import           Data.Maybe (mapMaybe, fromJust, isJust)
import           Data.Text.Lazy (pack)
import           GHC.IO (unsafePerformIO)
import           Control.Applicative
import qualified Hoca.Narrowing as N
import qualified Hoca.Problem as Problem
import           Hoca.Strategy
import           Hoca.Transform
import           Hoca.Utils (putDocLn, writeDocFile, render)
import qualified Hoca.PCF.Core as PCF
import Hoca.PCF.Sugar (programFromString, expressionFromString, Context, Exp)
import Hoca.PCF.Desugar (desugar, desugarExpression)
import Hoca.PCF.Core.DMInfer (infer)

type Problem = Problem.Problem Problem.Symbol Int
type Rule = R.ARule Problem.Symbol Int


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
  f && g = \ a -> f a && g a
  f || g = \ a -> f a || g a
  not f = not . f


cfa :: Problem :~> Problem
cfa = dfaInstantiate abstractP where
  abstractP _ _ [_] = True
  abstractP trl v _ =
    case R.rhs trl of
     Term.Var (w, _ :~> _) -> v == w
     rhs -> v `elem` T.headVars (ST.unType rhs)

cfa' :: Problem :~> Problem
cfa' = dfaInstantiate (\ _ _ _ -> False)

anyRule, caseRule, lambdaRule, fixRule, recursiveRule :: Problem -> Rule -> Bool
caseRule _ rl =
  case Problem.unlabeled <$> T.headSymbol (R.lhs rl) of
   Just Problem.Cond {} -> True
   _ -> False
lambdaRule _ rl = 
  case Problem.unlabeled <$> T.headSymbol (R.lhs rl) of
   Just Problem.Lambda {} -> True
   _ -> False
fixRule _ rl = 
  case Problem.unlabeled <$> T.headSymbol (R.lhs rl) of
   Just Problem.Fix {} -> True
   _ -> False
anyRule _ _ = True  
recursiveRule = Problem.isRecursive

definingRule :: String -> Problem -> Rule -> Bool
definingRule name _ rl =
  case T.headSymbol (R.lhs rl) of
   Just f -> render f == name
   _ -> False

oneOfIdx :: [Int] -> Problem -> Rule -> Bool
oneOfIdx is p r = maybe False (`elem` is) (Problem.indexOf p r)

leafRule :: Problem -> Rule -> Bool
leafRule p r = maybe True (null . Problem.cgSuccs p) (Problem.indexOf p r)

type NarrowedRule = N.NarrowedRule (T.ASym Problem.Symbol) Int Int

size :: T.ATerm f v -> Int
size = T.fold (const 1) (const ((+1) . sum))


sizeDecreasing :: Problem -> NarrowedRule -> Bool
sizeDecreasing _ ns = all (\ n -> sz (N.narrowing n) < sz (N.narrowedRule ns)) (N.narrowings ns) where
  sz rl = size (R.rhs rl)

sizeNonIncreasing :: Problem -> NarrowedRule -> Bool
sizeNonIncreasing _ ns = all (\ n -> sz (N.narrowing n) <= sz (N.narrowedRule ns)) (N.narrowings ns) where
  sz rl = size (R.lhs rl) + size (R.rhs rl)

branching :: Problem -> NarrowedRule -> Bool
branching _ ns = length (N.narrowings ns) > 1

selfInlining :: Problem -> NarrowedRule -> Bool
selfInlining _ ns = N.narrowedRule ns `elem` map N.narrowedWith (N.narrowings ns)

ruleDeleting :: Problem -> NarrowedRule -> Bool
ruleDeleting p ns =
  case nub (concatMap (Problem.cgPreds p) nwIds) of
   [i] -> i `notElem` nwIds
   _ -> False
   where
     nwIds = mapMaybe (Problem.indexOf p . N.narrowedWith) (N.narrowings ns)

withRule,onRule :: (Problem -> Rule -> Bool) -> Problem -> NarrowedRule -> Bool
withRule p rs = all (p rs) . map N.narrowedWith . N.narrowings
onRule p rs = p rs . N.narrowedRule

narrowWith,narrowOn,rewriteWith,rewriteOn :: (Problem -> Rule -> Bool) -> Problem :~> Problem
narrowWith = narrow . withRule
narrowOn = narrow . onRule
rewriteWith = rewrite . withRule
rewriteOn = rewrite . onRule

ur :: Problem :~> Problem
ur = usableRules >=> logMsg "USABLE"

cfaur :: Problem :~> Problem
cfaur =
  cfa >=> logMsg "CFA" >=> try ur
  
n1 :: Problem :~> Problem
n1 =
  try (exhaustive (rewrite (withRule lambdaRule) >=> logMsg "lambda"))
  >=> try (exhaustive (narrow (withRule caseRule) >=> logMsg "case"))
  >=> try ur

simplify :: Problem :~> Problem
simplify =
   try n1
   >=> toTRS
   >=> try (exhaustive (narrow (withRule leafRule)) >=> try usableRules)     
   >=> try (exhaustive ((narrow (sizeDecreasing || ruleDeleting) <=> cfa)
                        >=> try usableRules))
   >=> try compress

toTRS :: Problem :~> Problem   
toTRS = try cfa >=> try usableRules >=> uncurryRules >=> try usableRules


-- Interactive

data ST = EmptyState | Loaded Problem

instance PP.Pretty ST where
  pretty EmptyState = PP.text "No problem loaded"
  pretty (Loaded p) = PP.pretty p
    
data STATE = STATE { stCur :: ST
                   , stHist :: [ST]
                   , loaded :: Maybe Problem }


stateRef :: IORef STATE
stateRef = unsafePerformIO $ newIORef (STATE EmptyState [] Nothing)
{-# NOINLINE stateRef #-}

putState :: ST -> IO ()
putState st = do
  STATE cur hst ld <- readIORef stateRef
  let hst' =
        case cur of
         Loaded {} -> cur : hst
         _ -> hst 
  writeIORef stateRef (STATE st hst' ld)

getState :: IO ST
getState = stCur <$> readIORef stateRef

printState :: IO ()
printState = getState >>= putDocLn

modifyState :: (ST -> ST) -> IO ()
modifyState f = do
  st <- getState
  putState (f st)

programFromArgs :: FilePath -> Maybe String -> [String] -> IO (PCF.Program Context)
programFromArgs fname mname args = do
  r <- parseDesugared <$> readFile fname
  either (\e -> putErrLn e >> exitFailure) return r where
    parseDesugared s = do
      p <- programFromString fname s >>= desugar mname
      as <- sequence [ expressionFromString ("argument " ++ show i) ai >>= desugarExpression
                     | (i,ai) <- zip [(1::Int)..] args]
      return p { PCF.expression = foldl (PCF.App mempty) (PCF.expression p) as }
      
expressionFromArgs :: FilePath -> Maybe String -> [String] -> IO (PCF.Exp Context)
expressionFromArgs fn mn as = PCF.expression <$> programFromArgs fn mn as

programFromFile :: FilePath -> IO (PCF.Program Context)
programFromFile fname = programFromArgs fname Nothing []
      
load' :: FilePath -> IO ()
load' fn = do
  e <- expressionFromArgs fn Nothing []
  case run pcfToTrs e of
   Nothing -> putDocLn "Loading of problem failed."
   Just p -> writeIORef stateRef (STATE (Loaded p) [] (Just p))

load :: FilePath -> IO ()
load fn = load' fn >> printState

withProblemM :: (Problem -> IO a) -> IO a
withProblemM f = do
  st <- getState
  case st of
   EmptyState -> error "No problem loaded."
   Loaded p -> f p

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

dotCallGraph :: Maybe (Problem -> Rule -> Bool) -> IO (DotGraph Int)
dotCallGraph hl = withProblem mkGraph where
  mkGraph p = 
    GV.digraph' (mapM_ mkSCC (zip [0..] sccs))
    where
      sccs = map flattenSCC (stronglyConnCompR (Problem.toAssocList p))
      rs = Problem.rulesEnum p
      selectedNodes = [ i | (i,r) <- rs, maybe False (\ hl' -> hl' p r) hl]
      usableNodes = Problem.usableIdxs p selectedNodes
      reachSelectedNodes = [ j | (j,_) <- rs
                               , let us = Problem.usableIdxs p [j]
                               , any (`elem` us) selectedNodes ]
      highlightedNodes = selectedNodes ++ usableNodes

      mkSCC (k,scc) =
        GV.cluster (GV.Str $ pack $ "scc_" ++ show k) $
        forM scc $ \ (rl,i,ss) -> mkNode (i,rl) >> mapM (mkEdge i) ss
                       
      mkNode (i,r) = GV.node i nAttribs
        where nAttribs =
                shapeFor (T.headSymbol (R.lhs r))
                ++ highlighting
                ++ [ GVattribs.toLabel i, GVattribsc.Tooltip (pack (showRule r)) ]
              shapeFor (Just f)
                | Problem.isCaseSym f = [GVattribsc.Shape GVattribs.DiamondShape]
                | Problem.isFixSym f = [GVattribsc.Shape GVattribs.BoxShape]
                | Problem.isMainSym f = [GVattribsc.Shape GVattribs.House]
              shapeFor _ = []
              highlighting
                | i `elem` selectedNodes = [ GVattribs.fontColor GVSVG.White
                                           , GVattribs.fillColor GVSVG.RoyalBlue
                                           , GVattribs.style GVattribs.filled
                                           , GVattribs.color GVSVG.RoyalBlue]
                | i `elem` usableNodes = [GVattribs.color GVSVG.RoyalBlue
                                         , GVattribs.fontColor GVSVG.RoyalBlue]
                | isJust hl = [GVattribs.color GVSVG.Gray]
                | otherwise = []
                              
      mkEdge i j = GV.edge i j eAttribs
        where eAttribs
                | i `elem` highlightedNodes && j `elem` highlightedNodes =
                    GVattribs.color GVSVG.RoyalBlue : [ GVattribs.style GVattribs.dashed | j `notElem` reachSelectedNodes]
                | otherwise = []
     -- legendM = GV.graphAttrs [GVattribs.toLabel (concatMap (\ (i,r) -> show i ++ ": " ++ showRule r) rs) ]
      showRule rl =
        PP.displayS (PP.renderSmart 1.0 80 (ppTerm lhs PP.<+> PP.text "->" PP.<+> ppTerm rhs)) []
        where
          lhs = R.lhs rl
          rhs = R.rhs rl
          ppTerm = T.prettyTerm PP.pretty ppVar
          ppVar i = PP.text "x" PP.<> PP.int i

saveCG :: Maybe (Problem -> Rule -> Bool) -> FilePath -> IO ()
saveCG hl fp = do
  g <- dotCallGraph hl
  void (runGraphviz g Svg fp)
  
viewGraph :: Maybe (Problem -> Rule -> Bool) -> IO ()
viewGraph hl = dotCallGraph hl >>= flip runGraphvizCanvas' Xlib

state :: IO ()
state = printState             

reset :: IO ()
reset = do 
  STATE _ _ lp <- readIORef stateRef
  case lp of
   Nothing -> error "No problem loaded."
   Just p -> putState (Loaded p) >> printState
  
undo' :: IO Bool
undo' = do
  STATE _ hst lp <- readIORef stateRef 
  case hst of 
   [] -> return False
   (h:hs) -> do 
     writeIORef stateRef (STATE h hs lp)
     return True

undo :: IO ()
undo = do undone <- undo' 
          if undone 
            then printState
            else putDocLn (PP.text "Nothing to undo")

apply :: (Problem :~> Problem) -> IO ()
apply m = do 
  st <- getState  
  case st of
   EmptyState ->
     putDocLn (PP.vcat [ PP.text "No system loaded."
                       , PP.text ""
                       , PP.text "Use 'load <filename>' to load a new problem."])
   Loaded p ->
     case run m p of
      Nothing -> putDocLn "Transformation inapplicable."
      Just r -> putState (Loaded r) >> printState



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
     e <- expressionFromArgs fname Nothing as
     putDocLn (PP.pretty (fromJust (PCF.nf PCF.cbv e)))
   "--eval" : _ -> putStrLn helpMsg
   "--pcf" : fname : [] -> do
     e <- expressionFromArgs fname Nothing []
     putDocLn (PP.pretty e)
   "--pcf" : _ -> putStrLn helpMsg     
   "--no-simp" : fname : [] -> 
     transform False fname Nothing
   "--no-simp" : fname : name : [] -> 
     transform False fname (Just name)
   "--no-simp" : _ -> putStrLn helpMsg          
   fname : []  ->
     transform True fname Nothing
   fname : name : []  ->
     transform True fname (Just name)
   _ -> error helpMsg
  exitSuccess
  where
    transform doSimp fname mname = do
      e <- expressionFromArgs fname mname []
      case run tr e of
       Just prob -> putDocLn (Problem.prettyWST prob)
       Nothing -> do
         putErrLn "the program cannot be transformed"
         exitFailure
      where
        tr | doSimp = pcfToTrs >=> simplify
           | otherwise = pcfToTrs

norm p = p { PCF.expression = fromJust $ PCF.nf step (PCF.expression p)} where
     step = \ e -> PCF.beta e <|> PCF.fixCBV e <|> PCF.cond e

typeProgram p = 
    case infer p of 
      Left e -> putDocLn e >> error "program not typable"
      Right p' -> putDocLn (PCF.typeOf (PCF.expression p')) >> return p'
                
-- TODO
s = save "/home/zini/op.trs" >> saveCG Nothing "/home/zini/op.svg"
a p = apply p >> s
sel p = save "/home/zini/op.trs" >> saveCG (Just p) "/home/zini/op.svg" >> void (select p)

