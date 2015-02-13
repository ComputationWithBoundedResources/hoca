#!/usr/local/bin/runhaskell
module Main where
import Prelude hiding ((&&),(||), not)
import qualified Prelude as Prelude
import           Control.Applicative (Applicative (..),Alternative (..), (<$>))
import           Control.Monad (foldM, void)
import qualified Hoca.FP as FP
import qualified Hoca.PCF as PCF
import qualified Hoca.Narrowing as N
import qualified Hoca.UsableRules as UR
import qualified Hoca.Problem as Problem
import qualified Hoca.ATRS as ATRS
import           Hoca.Utils (putDocLn, writeDocFile, render)
import           Hoca.Transform
import           System.Environment (getArgs)
import           System.IO (hPutStrLn, stderr)
import GHC.IO (unsafePerformIO)
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Data.Maybe (fromJust, isJust)
import qualified Data.Rewriting.Rule as R
import qualified Data.Rewriting.Term as T
import System.Exit (exitSuccess,exitFailure)
import Data.GraphViz.Commands
import qualified Data.GraphViz.Types.Monadic as GV
import Data.GraphViz.Types.Generalised (DotGraph)
import qualified Data.GraphViz.Attributes as GVattribs
import qualified Data.GraphViz.Attributes.Complete as GVattribsc
import Data.Text.Lazy (pack)
import Control.Monad (guard, MonadPlus)
import qualified Data.GraphViz.Attributes.Colors.SVG as GVSVG
import qualified Data.MultiSet as MS



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
cfa = dfaInstantiate abstractP where
  abstractP _ _ [_] = True
  abstractP trl v _ =
    case R.rhs trl of
     T.Var (w, _ ATRS.:~> _) -> v == w
     rhs -> v `elem` ATRS.headVars (ATRS.unType rhs)
  --   (R.rhs -> T.Var (w, _ ATRS.:~> _)) v _ = 
  -- abstractP trl v _ =  v `elem` ATRS.headVars (R.rhs (ATRS.unTypeRule trl))

-- dfa :: PCF.Strategy m => Problem -> m Problem
-- dfa = dfaInstantiate (R.vars . ATRS.unTypeRule)       

size :: T.Term f v -> Int
size = T.fold (const 1) (const ((+1) . sum))

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

oneOfIdx :: [Int] -> Problem -> Rule -> Bool
oneOfIdx is p r = maybe False (`elem` is) (Problem.indexOf p r)

leafRule :: Problem -> Rule -> Bool
leafRule p n = null (Problem.callees p n)

-- branching  :: Problem -> Rule -> Bool
-- branching p n = length (Problem.callees p n) >= 1

type NarrowedRule = N.NarrowedRule (ATRS.ASym Problem.Symbol) Int Int

sizeDecreasing :: Problem -> NarrowedRule -> Bool
sizeDecreasing _ ns = all (\ n -> sz (N.narrowing n) < sz (N.narrowedRule ns)) (N.narrowings ns) where
  sz rl = size (R.lhs rl) + size (R.rhs rl)

sizeNonIncreasing :: Problem -> NarrowedRule -> Bool
sizeNonIncreasing _ ns = all (\ n -> sz (N.narrowing n) <= sz (N.narrowedRule ns)) (N.narrowings ns) where
  sz rl = size (R.lhs rl) + size (R.rhs rl)

complexityPreserving :: Problem -> NarrowedRule -> Bool
complexityPreserving p nr =
  all (redexReflecting . N.narrowedWith) (N.narrowings nr)
  || argumentNormalised (N.narrowSubterm nr) where
  redexReflecting rl = varsMS (R.rhs rl) `MS.isSubsetOf` varsMS (R.lhs rl) where
    varsMS = MS.fromList . T.vars
  argumentNormalised (T.Fun _ ts) = null (UR.usableRules ts (Problem.rules p))
  argumentNormalised _ = True


branching :: Problem -> NarrowedRule -> Bool
branching _ ns = length (N.narrowings ns) > 1

selfInlining :: Problem -> NarrowedRule -> Bool
selfInlining _ ns = N.narrowedRule ns `elem` map N.narrowedWith (N.narrowings ns)

withRule,onRule :: (Problem -> Rule -> Bool) -> Problem -> NarrowedRule -> Bool
withRule p rs = all (p rs) . map N.narrowedWith . N.narrowings
onRule p rs = p rs . N.narrowedRule

narrowWith,narrowOn :: (Monad m, Applicative m, Alternative m) => (Problem -> Rule -> Bool) -> Problem -> m Problem
narrowWith = narrow . withRule
narrowOn = narrow . withRule


provided :: MonadPlus m => (Problem -> m Problem) -> (Problem -> Problem -> Bool) -> Problem -> m Problem
provided t f p = do
  p' <- t p
  guard (f p p')
  return p'

-- provided :: MonadPlus m => (Problem -> m Problem) -> (Problem -> Bool) -> Problem -> m Problem
-- provided t f p = do
--   p' <- t p
--   guard (f p')
--   return p
-- -- providedRel :: MonadPlus m => (Problem -> Problem -> m Problem) -> (Problem -> Bool) -> Problem -> m Problem
-- providedRel :: MonadPlus m => (Problem -> m Problem) -> (Problem -> Problem -> Bool) -> Problem -> m Problem
-- providedRel t f p = provided t (f p) p



-- n1 :: PCF.Strategy m => Problem -> m Problem
-- n1 = exhaustive ((narrow (withRule caseRule) >=> traceProblem "case narrowing")
--                  <=> (rewrite (withRule lambdaRule) >=> traceProblem "lambda rewrite"))
--      >=> exhaustive (rewrite (withRule fixRule) >=> traceProblem "fix rewrite")
--      >=> try usableRules >=> try neededRules          
--      >=> exhaustive (narrow (withRule (not recursiveRule)) >=> traceProblem "non-recursive narrowing")
--      >=> try usableRules >=> try neededRules


-- t1 :: PCF.Strategy m => Problem -> m Problem
-- t1 =
--   exhaustive ((narrow (withRule caseRule) >=> traceProblem "case narrowing")
--               <=> narrow sizeDecreasing >=> traceProblem "size-decreasing narrowing")
--   >=> cfa >=> try usableRules >=> try neededRules >=> traceProblem "CFA"
--   >=> try uncurryRules >=> try usableRules >=> try neededRules >=> traceProblem "uncurried"
--   >=> exhaustive (narrow sizeDecreasing >=> traceProblem "size-decreasing narrowing")

n1 :: PCF.Strategy m => Problem -> m Problem
n1 =
  exhaustive (narrowWith caseRule)
  >=> exhaustive (narrowWith fixRule)
  >=> try usableRules

t1 :: PCF.Strategy m => Problem -> m Problem
t1 = cfa >=> uncurryRules >=> usableRules
  
  
n2 :: PCF.Strategy m => Problem -> m Problem
n2 = narrow (complexityPreserving && (sizeNonIncreasing && not branching
                                      || sizeDecreasing
                                      || withRule leafRule))
     >=> try usableRules

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

-- narrowConst :: PCF.Strategy m => Problem -> m Problem
-- narrowConst =
--   narrow (\ _ ns -> all (decreasingConst (N.narrowSubterm ns) . N.narrowing) (N.narrowings ns))
--   >=> try usableRules >=> try neededRules
--   where
--     decreasingConst t (R.Rule _ r) =
--       T.isGround t
--       || (not (null as) && all (any (\ (li,ri) -> isConstantTerm li && isConstantTerm ri && size li > size ri)) as)
--       where
--         as = [ zip (ATRS.args t) (ATRS.args ri)
--              | ri <- T.subterms r, ATRS.headSymbol t == ATRS.headSymbol ri ]
--     -- decreasingConst t@(T.Fun f ts) (R.Rule l r) = T.isGround t 
--       -- null as || all (any (\ (li,ri) -> isConstantTerm li && isConstantTerm ri && size li > size ri)) as where
--       --   as = [ zip ts rs
--       --        | T.Fun g rs <- T.subterms r, f == g ]

--     isConstantTerm t = T.isGround t && all isConstructor (ATRS.funs t) where 
--       isConstructor Problem.Con{} = True
--       isConstructor _ = False

--     size = T.fold (const (1::Int)) (const (succ . sum))
--     -- T.Var {} `embeds` _ = False
--     -- s@(T.Fun f ss) `embeds` t@(T.Fun g ts) =
--     --   t `elem` (T.properSubterms s)
--     --   || (f == g && 



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

load' :: FilePath -> IO ()
load' fn = do
  mp <- pcfToTrs <$> expressionFromArgs fn []
  case mp of
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
  mkGraph p = GV.digraph' $ do
       mapM_ mkNode rs
       mapM_ mkEdges rs 
    where 
      rs = Problem.rulesEnum p
      selectedNodes = [ i | (i,r) <- rs, maybe False (\ hl' -> hl' p r) hl]
      usableNodes = Problem.usableIdxs p selectedNodes
      reachSelectedNodes = [ j | (j,_) <- rs, let us = Problem.usableIdxs p [j], any (`elem` us) selectedNodes ]
      highlightedNodes = selectedNodes ++ usableNodes
      mkNode (i,r) = GV.node i nAttribs
        where nAttribs =
                shapeFor (ATRS.headSymbol (R.lhs r))
                ++ highlighting
                ++ [ GVattribs.toLabel i, GVattribsc.Tooltip (pack (showRule r)) ]
              shapeFor (Just f)
                | Problem.isCaseSym f = [GVattribsc.Shape GVattribs.DiamondShape]
                | Problem.isFixSym f = [GVattribsc.Shape GVattribs.BoxShape]
                | Problem.isMainSym f = [GVattribsc.Shape GVattribs.House]
              shapeFor _ = []
              highlighting
                | i `elem` selectedNodes = [GVattribs.style GVattribs.bold
                                           , GVattribs.fontColor GVSVG.RoyalBlue
                                           , GVattribs.fillColor GVSVG.SkyBlue
                                           , GVattribs.color GVSVG.RoyalBlue]
                | i `elem` usableNodes = [GVattribs.color GVSVG.RoyalBlue
                                         , GVattribs.fontColor GVSVG.RoyalBlue]
                | isJust hl = [GVattribs.color GVSVG.Gray]
                | otherwise = []
                              
      mkEdges (i,_) = mapM_ (\ j -> GV.edge i j (eAttribs j)) (Problem.calleeIdxs p i)
        where eAttribs j
                | i `elem` highlightedNodes && j `elem` highlightedNodes =
                    [GVattribs.color GVSVG.RoyalBlue] ++ [ GVattribs.style GVattribs.dashed | j `notElem` reachSelectedNodes]
                | otherwise = []
     -- legendM = GV.graphAttrs [GVattribs.toLabel (concatMap (\ (i,r) -> show i ++ ": " ++ showRule r) rs) ]
      showRule (R.Rule lhs rhs) = showTerm lhs ++ " -> " ++ showTerm rhs
        where
          showTerm t = [c | c <- show (T.prettyTerm PP.pretty ppVar t), c /= '\n', c /= ' ']
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

apply :: (Problem -> Maybe Problem) -> IO ()
apply m = do 
  st <- getState  
  case st of
   EmptyState ->
     putDocLn (PP.vcat [ PP.text "No system loaded."
                       , PP.text ""
                       , PP.text "Use 'load <filename>' to load a new problem."])
   Loaded p ->
     case m p of
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
