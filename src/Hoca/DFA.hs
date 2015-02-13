module Hoca.DFA (
  NonTerminal (..)
  , DFAProduction
  , DFAGrammar
  , startNonTerminal
  , auxNonTerminal
  , refinements
  ) where

import qualified Data.Rewriting.Term as T
import qualified Data.Rewriting.Rule as R
import Hoca.Utils (runVarSupply, fresh, andM, orM, tracePretty, tracePretty')
import Hoca.TreeGrammar
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.List as L

import qualified Text.PrettyPrint.ANSI.Leijen as PP
import qualified Data.Rewriting.Substitution.Type as ST
import qualified Data.Rewriting.Substitution as S
import Control.Applicative ((<$>))
import Data.Maybe (fromJust)
import Control.Monad (MonadPlus (..), msum, when, unless)
import Control.Monad.Trans (lift)
import Control.Monad.State.Lazy (execState, execStateT, get, modify)

data NonTerminal v x = X x | V v Int | R Int deriving (Ord, Eq, Show)

type DFAProduction f v x = Production f (NonTerminal v x)
type DFAGrammar f v x = Grammar f (NonTerminal v x)

instance (PP.Pretty x, PP.Pretty v) => PP.Pretty (NonTerminal x v) where
  pretty (X s) = PP.text "X" PP.<> PP.braces (PP.pretty s)
  pretty (V s i) = PP.text "V" PP.<> PP.braces (PP.text "x" PP.<> PP.pretty s PP.<> PP.text "_" PP.<> PP.int i) 
  pretty (R i) = PP.text "R" PP.<> PP.braces (PP.int i)
  
startNonTerminal :: NonTerminal v x
startNonTerminal = R 0

auxNonTerminal :: x -> NonTerminal v x
auxNonTerminal = X

liftTerm :: Int -> T.Term f v -> Term f (NonTerminal v x)
liftTerm i (T.Var v) = NonTerminal (V v i)
liftTerm i (T.Fun f ts) = Terminal f (map (liftTerm i) ts)

unliftTerm :: Term f (NonTerminal v x) -> T.Term f ()
unliftTerm (Terminal f ts) = T.Fun f (map unliftTerm ts)
unliftTerm _ = T.Var ()               


type Ctxt t n = Term t n -> Term t n

contexts :: Term t n -> [(Ctxt t n, Term t n)]
contexts = walk id
  where
    walk c n@NonTerminal{} = [(c,n)]
    walk c t@(Terminal f ts) =
      (c, t) : concatMap (\ (ls,ti,rs) ->
                           walk (\ t' -> c(Terminal f (ls ++ [t'] ++ rs))) ti)
                 (parts [] ts)

    parts _ [] = []
    parts ls (t:rs) = (ls,t,rs) : parts (ls ++ [t]) rs

newtype Match f v x = Match [DFAProduction f v x] deriving Show
data Matches f v x =
  Matches { matchedRule :: (R.Rule f v, Int)
          , matches :: [Match f v x] }
  deriving Show

minimalMatches :: (Ord x, Ord v, Ord f) => DFAGrammar f v x -> Term f (NonTerminal v x) -> (Int,R.Rule f v) -> Matches f v x
minimalMatches tg s (i, rl@(R.Rule lhs _)) =
     Matches { matchedRule = (rl, i)
             , matches = map Match (minMatches lhs s)}
  where
    minMatches (T.Var v) u = return [Production (V v i) u]
    minMatches (T.Fun f ls) (Terminal g vs)
      | f /= g    = mzero
      | otherwise = concat <$> sequence [minMatches li vi | (li,vi) <- zip ls vs]
    minMatches t (NonTerminal n)
      = msum [ minMatches t r | r <- produces' tg n]

extensionOf :: (Ord v, Ord f, Ord x)
               => DFAGrammar f v x -> [(Int,R.Rule f v)] -> NonTerminal v x
               -> (Ctxt f (NonTerminal v x), Term f (NonTerminal v x))
               -> [Production f (NonTerminal v x)]
extensionOf tg prog lhs (ctx,t) =
  concatMap mkExts (map (minimalMatches tg t) prog) where
  mkExts match
    | null (matches match) = []
    | otherwise = 
        Production lhs (ctx (NonTerminal (R i)))
        : Production (R i) (liftTerm i (R.rhs rl))
        : [ p | Match m <- matches match, p <- m ]
    where (rl,i) = matchedRule match

complete :: (Ord f, Ord x, Ord v) => [(Int, R.Rule f v)] -> DFAGrammar f v x -> DFAGrammar f v x
complete prog = exec (fixM makeClosure) where

  exec m = execState (execStateT (execStateT m S.empty) True)
  setModified = lift . modify . const

  currentTG = lift (lift get)

  addProductions = mapM_ insertTG where
    insertTG p = do
      isElt <- member p <$> currentTG
      unless isElt $ do
        lift (lift (modify (insert p)))
        setModified True

  fixM op = do
    setModified False
    (toList <$> currentTG) >>= mapM_ op
    modified <- lift get 
    when modified (fixM op)

  makeClosure (Production lhs rhs) = do
    tg <- currentTG
    mapM_ (closeSubterm tg) (contexts rhs)
    where
      closeSubterm tg (ctx,t@(Terminal _ args)) = do 
        argNormalised <- andM [ not <$> reducible ai | ai <- args]
        when argNormalised (addProductions (extensionOf tg prog lhs (ctx,t)))
      closeSubterm _ _ = return ()

  -- reducible s == all terms represented by s are reducible
  reducible (NonTerminal n@(R _)) = do
    tg <- currentTG
    andM [ reducible' rhs | rhs <- produces tg n ]
  reducible g = reducible' g
  
  reducible' = withMemoR red where
    red t@(Terminal _ ts) = do
      tg <- currentTG
      ra <- orM [ reducible' ti | ti <- ts ]
      return (ra || any (not . null . matches . minimalMatches tg t) prog)
    red _ = return False
    
    withMemoR m t = do
      withNF <- get
      if t `S.member` withNF
        then return False
        else do
        r <- m t
        unless r (modify (S.insert t))
        return r

refinements :: (PP.Pretty x, PP.Pretty v, PP.Pretty f, Ord v, Ord f, Ord x) => [(Int, R.Rule f v)] -> DFAGrammar f v x -> Int -> (v -> [R.Term f ()] -> Bool) -> ([R.Rule f Int], [Int])
refinements prog initial = 
  \ i refineP ->
   case L.lookup i prog of
    Nothing -> ([],[])
    Just rl@(R.Rule lhs rhs) -> ([R.Rule (s `apply` lhs) (s `apply` rhs) | s <- substs]
                                , [j | (R j) <- reachableRules (R i) ])
      where
        apply s t = fromJust (S.gApply s t)
        substs = map toSubst (foldl (\ l v -> [ (v,p):s | s <- l, p <- patterns v]) [[]] (L.nub (R.vars rl))) where 
          patterns v
            | refineP v assigns = assigns
            | otherwise = [T.Var ()]
            where assigns = L.nub (map unliftTerm (reducts (V v i)))
  where
    tg = tracePretty' (complete prog initial)
    reducts s =
      case produces' tg s of 
       [] -> [NonTerminal s]
       rhss -> rhss

    toSubst = ST.fromMap . M.fromList . runVarSupply . mapM (\ (v,p) -> (,) v <$> ren p)
      where
        ren (T.Fun f ts) = T.Fun f <$> mapM ren ts
        ren _            = T.Var <$> fresh

    reachableRules = concatMap nonTerminals . produces tg
      -- succs r where -- walk [] (succs r) where
      -- succs = concatMap nonTerminals . produces tg
      -- walk _ [] = []
      -- walk vis (n@R{}:ns) = n : walk (n:vis) ns
      -- walk vis (n:ns)
      --   | n `elem` vis = walk vis ns
      --   | otherwise = succs n ++ walk (n:vis) (ms ++ ns) where
      --       ms = succs n


