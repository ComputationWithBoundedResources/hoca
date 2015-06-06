{-# LANGUAGE ViewPatterns, TypeOperators, FlexibleContexts #-}
#!/usr/local/bin/runhaskell
-- TEMPORARY / integrate in tct3 later
module Main where


import           Control.Applicative
import           Control.Monad (foldM, void, forM)
import           Data.Either (either)
import           Data.Graph (flattenSCC, stronglyConnCompR)
import qualified Data.GraphViz.Attributes as GVattribs
import qualified Data.GraphViz.Attributes.Colors.SVG as GVSVG
import qualified Data.GraphViz.Attributes.Complete as GVattribsc
import           Data.GraphViz.Commands
import           Data.GraphViz.Types.Generalised (DotGraph)
import qualified Data.GraphViz.Types.Monadic as GV
import           Data.IORef (IORef, newIORef, readIORef, writeIORef)
import qualified Data.IntMap as IMap
import           Data.List (nub)
import           Data.Maybe (mapMaybe, fromJust, isJust)
import           Data.Monoid (mempty)
import           Data.Rewriting.Applicative.Rule
import           Data.Rewriting.Applicative.Term
import           Data.Text.Lazy (pack)
import           GHC.IO (unsafePerformIO)
import           Hoca.Data.MLTypes
import qualified Hoca.PCF.Core as PCF
import qualified Hoca.PCF.Core.DMInfer as DM
import           Hoca.PCF.Desugar (desugar, desugarExpression)
import           Hoca.PCF.Sugar (programFromString, expressionFromString, Context, Exp)
import qualified Hoca.Problem as P
import           Hoca.Problem hiding (Problem,TRule)
import           Hoca.Transform
import           Hoca.Transform.Defunctionalize
import           Hoca.Utils (putDocLn, writeDocFile, render)
import qualified Prelude
import           Prelude hiding ((&&),(||), not)
import           System.Environment (getArgs)
import           System.Exit (exitSuccess,exitFailure)
import           System.IO (hPutStrLn, stderr)
import qualified Text.PrettyPrint.ANSI.Leijen as PP

type Problem = P.Problem Symbol Int
type TRule = P.TRule Symbol Int

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


headSymbolSatisfies :: (Symbol -> Bool) -> Problem -> ARule Symbol Int -> Bool
headSymbolSatisfies p _ rl = 
  case unlabeled <$> headSymbol (lhs rl) of
   Just f -> p f
   _ -> False

anyRule, caseRule, lambdaRule, fixRule :: Problem -> ARule Symbol Int -> Bool 
caseRule = headSymbolSatisfies p where 
   p Cond {} = True
   p _ = False

lambdaRule = headSymbolSatisfies p where 
   p Lambda {} = True
   p _ = False

fixRule = headSymbolSatisfies p where 
   p Fix {} = True
   p _ = False
anyRule _ _ = True  

definingRule :: String -> Problem -> TRule -> Bool
definingRule name _ (theRule -> rl) = 
  case unlabeled <$> headSymbol (lhs rl) of
   Just f -> render f == name
   _ -> False

-- recursiveRule = isRecursive


-- oneOfIdx :: [Int] -> Problem -> Rule -> Bool
-- oneOfIdx is p r = maybe False (`elem` is) (indexOf p r)

leafRule :: (Eq f, Eq v) => P.Problem f v -> ARule f v -> Bool
leafRule p r = maybe True (null . cgSuccs p) (indexOf p r)


tsize :: ATerm f v -> Int
tsize = fold (const 1) (const ((+1) . sum))

type NR f v = NarrowedRule (ASym f) v v 
sizeDecreasing :: P.Problem f v -> NR f v -> Bool
sizeDecreasing _ ns = all (\ n -> sz (narrowing n) < sz (narrowedRule ns)) (narrowings ns) where
  sz rl = tsize (rhs rl)

-- sizeNonIncreasing :: Problem -> NarrowedRule -> Bool
-- sizeNonIncreasing _ ns = all (\ n -> sz (N.narrowing n) <= sz (N.narrowedRule ns)) (N.narrowings ns) where
--   sz rl = size (R.lhs rl) + size (R.rhs rl)

-- branching :: Problem -> NarrowedRule -> Bool
-- branching _ ns = length (N.narrowings ns) > 1

-- selfInlining :: Problem -> NarrowedRule -> Bool
-- selfInlining _ ns = N.narrowedRule ns `elem` map N.narrowedWith (N.narrowings ns)

ruleDeleting :: (Eq f, Eq v) => P.Problem f v-> NR f v -> Bool
ruleDeleting p ns =
  case nub (concatMap (cgPreds p) nwIds) of
   [i] -> i `notElem` nwIds
   _ -> False
   where
     nwIds = mapMaybe (indexOf p . narrowedWith) (narrowings ns)

-- withRule,onRule :: (Problem -> Rule -> Bool) -> Problem -> NarrowedRule -> Bool
-- withRule p rs = all (p rs) . map N.narrowedWith . N.narrowings
-- onRule p rs = p rs . N.narrowedRule

-- narrowWith,narrowOn,rewriteWith,rewriteOn :: (Problem -> Rule -> Bool) -> Problem :~> Problem
-- narrowWith = narrow . withRule
-- narrowOn = narrow . onRule
-- rewriteWith = rewrite . withRule
-- rewriteOn = rewrite . onRule

-- ur :: Problem :~> Problem
-- ur = usableRules >=> logMsg "USABLE"

-- cfaur :: Problem :~> Problem
-- cfaur =
--   cfa >=> logMsg "CFA" >=> try ur

ur :: Eq f => P.Problem f Int :=> P.Problem f Int
ur = usableRulesSyntactic >=> logMsg "UR"

cfa :: Problem :=> Problem
cfa = instantiate abstractP >=> logMsg "CFA" where
  abstractP _ _ [_] = True
  abstractP trl v _ = 
    maybe False isTArrow (lookup v (theEnv trl)) 
    && (var v == r || v `elem` headVars r) 
    where
      r = rhs (theRule trl)

simplifyATRS :: P.Problem Symbol Int :=> P.Problem Symbol Int
simplifyATRS =
  try (exhaustive (rewrite (withRule lambdaRule) >=> logMsg "lambda"))
  >=> try (exhaustive (inline (withRule caseRule) >=> logMsg "case"))
  >=> try ur

toTRS :: P.Problem Symbol Int :=> P.Problem Symbol Int
toTRS = try cfa >=> try ur >=> uncurried >=> try ur

urDFA :: P.Problem Symbol Int :=> P.Problem Symbol Int
urDFA = usableRulesDFA >=> logMsg "UR-DFA"

simplifyTRS :: P.Problem Symbol Int :=> P.Problem Symbol Int
simplifyTRS = 
  try (exhaustive (inline (withRule leafRule)) >=> try ur) 
  >=> try (exhaustive ((inline (sizeDecreasing || ruleDeleting) <=> urDFA) >=> try ur))

simplify :: P.Problem Symbol Int :=> P.Problem Symbol Int
simplify = try simplifyATRS >=> toTRS >=> try simplifyTRS >=> try compress

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
      
-- expressionFromArgs :: FilePath -> Maybe String -> [String] -> IO (PCF.Exp Context)
-- expressionFromArgs fn mn as = PCF.expression <$> programFromArgs fn mn as

programFromFile :: FilePath -> IO (PCF.Program Context)
programFromFile fname = programFromArgs fname Nothing []

defunctionalizedFromFile :: FilePath -> Maybe String -> [String] -> IO Problem
defunctionalizedFromFile fn m a = do
  prog <- programFromArgs fn m a 
  case DM.infer prog of 
    Left e -> putDocLn e >> error "Typing failed!"
    Right prog' -> 
      case run defunctionalize prog' of 
        Nothing -> error "Defunctionalization failed!"
        Just p -> return p
      
load' :: FilePath -> IO ()
load' fn = do 
  p <- defunctionalizedFromFile fn Nothing []
  writeIORef stateRef (STATE (Loaded p) [] (Just p))

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

select :: (Problem -> ARule Symbol Int -> Bool) -> IO [TRule]
select f = withProblemM sel where
  sel p  = do
    let rs = [ e | e@(_,rl) <- rulesEnum p, f p (theRule rl)]
    putDocLn (restrictIdx (map fst rs) p)
    putDocLn PP.empty
    return (map snd rs)

save :: FilePath -> IO ()
save fn = withProblemM (writeDocFile fn . prettyWST)

dotCallGraph :: Maybe (Problem -> ARule Symbol Int -> Bool) -> IO (DotGraph Int)
dotCallGraph hl = withProblem mkGraph where
  mkGraph p = 
    GV.digraph' (mapM_ mkSCC (zip [0..] sccs))
    where
      sccs = map flattenSCC (stronglyConnCompR (toAssocList p))
      rs = rulesEnum p
      selectedNodes = [ i | (i,r) <- rs, maybe False (\ hl' -> hl' p (theRule r)) hl]
      usableNodes = usableIdx p selectedNodes
      reachSelectedNodes = [ j | (j,_) <- rs
                               , let us = usableIdx p [j]
                               , any (`elem` us) selectedNodes ]
      highlightedNodes = selectedNodes ++ usableNodes

      mkSCC (k,scc) =
        GV.cluster (GV.Str $ pack $ "scc_" ++ show k) $
        forM scc $ \ (rl,i,ss) -> mkNode (i,rl) >> mapM (mkEdge i) ss
                       
      mkNode (i,theRule -> r) = GV.node i nAttribs
        where nAttribs =
                shapeFor (headSymbol (lhs r))
                ++ highlighting
                ++ [ GVattribs.toLabel i, GVattribsc.Tooltip (pack (showRule r)) ]
              shapeFor (Just f)
                | isCaseSym f = [GVattribsc.Shape GVattribs.DiamondShape]
                | isFixSym f = [GVattribsc.Shape GVattribs.BoxShape]
                | isMainSym f = [GVattribsc.Shape GVattribs.House]
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
        PP.displayS (PP.renderSmart 1.0 80 (ppTerm (lhs rl) PP.<+> PP.text "->" PP.<+> ppTerm (rhs rl))) []
        where
          ppTerm = prettyTerm PP.pretty ppVar
          ppVar i = PP.text "x" PP.<> PP.int i

saveCG :: Maybe (Problem -> ARule Symbol Int -> Bool) -> FilePath -> IO ()
saveCG hl fp = do
  g <- dotCallGraph hl
  void (runGraphviz g Svg fp)
  
viewGraph :: Maybe (Problem -> ARule Symbol Int -> Bool) -> IO ()
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

apply :: (Problem :=> Problem) -> IO ()
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
     e <- PCF.expression <$> programFromArgs fname Nothing as
     putDocLn (PP.pretty (fromJust (PCF.nf PCF.cbv e)))
   "--eval" : _ -> putStrLn helpMsg
   "--pcf" : fname : [] -> do
     p <- programFromArgs fname Nothing []
     case DM.infer p of 
       Left e -> putDocLn (PP.pretty p) >> putDocLn e
       Right p' -> putDocLn (PP.pretty p')
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
      prob <- defunctionalizedFromFile fname mname []
      let r = if doSimp then run simplify prob else Just prob
      case r of 
       Just prob' -> putDocLn (prettyWST prob')
       Nothing -> do
         putErrLn "the program cannot be transformed"
         exitFailure

norm p = p { PCF.expression = fromJust $ PCF.nf step (PCF.expression p)} where
     step = \ e -> PCF.beta e <|> PCF.fixCBV e <|> PCF.cond e

typeProgram p = 
    case DM.infer p of 
      Left e -> putDocLn e >> error "program not typable"
      Right p' -> putDocLn (PCF.typeOf (PCF.expression p')) >> return p'
                
-- TODO
s = save "/home/zini/op.trs" >> saveCG Nothing "/home/zini/op.svg"
a p = apply p >> s
sel p = save "/home/zini/op.trs" >> saveCG (Just p) "/home/zini/op.svg" >> void (select p)

simp = simplifyATRS >=> cfa
