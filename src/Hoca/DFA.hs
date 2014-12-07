module Hoca.DFA
       ( TGSym (..)
       , TGTerm
       , TGRule (..)
       , fromRules
       , startSymbol
       , auxSymbol
       , fun
       , terminal
       , TG
       , refinements)
       where

import qualified Data.Rewriting.Term as T
import Data.Rewriting.Term (Term (..))
import qualified Data.Rewriting.Rule as R
import qualified Data.Rewriting.Rules as RS
import qualified Data.Rewriting.Context as C
import Hoca.Utils (contexts, prod, runVarSupply, fresh, tracePretty', tracePretty)
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.List as L

import qualified Text.PrettyPrint.ANSI.Leijen as PP
import qualified Data.Rewriting.Substitution.Type as ST
import qualified Data.Rewriting.Substitution as S
import Control.Applicative ((<$>))
import Data.Maybe (fromJust)
import Control.Monad (MonadPlus (..), msum)
import Control.Monad.State.Lazy (execState, execStateT, get, modify)
import Control.Monad (when)
import Control.Monad.Trans (lift)
import Control.Monad (unless)
import Control.Applicative ((<*>))
import Control.Monad (forM)
import Data.Maybe (fromMaybe)

data TGSym f v x = F f
                 | X x
                 | V v Int
                 | R Int
                 deriving (Ord, Eq, Show)

pattern Data x = Fun (X x) []
pattern Substitution v i = Fun (V v i) []
pattern Result i = Fun (R i) []
pattern Term f ts = Fun (F f) ts


instance (PP.Pretty f, PP.Pretty v, PP.Pretty x) => PP.Pretty (TGSym f v x) where
  pretty (F s) = PP.pretty s
  pretty (X s) = PP.text "X" PP.<> PP.braces (PP.pretty s)
  pretty (V s i) = PP.text "V" PP.<> PP.braces (PP.text "x" PP.<> PP.pretty s PP.<> PP.text "_" PP.<> PP.int i) 
  pretty (R i) = PP.text "R" PP.<> PP.braces (PP.int i)
  
type TGTerm f v x = Term (TGSym f v x) ()
data TGRule f v x = Rule (TGSym f v x) (Term (TGSym f v x) ())
                    deriving (Eq, Ord, Show)

type TG f v x = M.Map (TGSym f v x) [TGTerm f v x]

(-->) :: TGSym f v x -> Term (TGSym f v x) () -> TGRule f v x
(-->) = Rule

productions :: (Ord f, Ord v, Ord x) => TG f v x -> TGSym f v x -> [TGTerm f v x]
productions tg lhs = fromMaybe [] (M.lookup lhs tg)


productions' :: (Ord f, Ord v, Ord x) => TG f v x -> TGSym f v x -> [TGTerm f v x]
productions' tg lhs = walk [] [lhs] where
  walk vis [] = []
  walk vis (n:ns)
    | n `elem` vis = walk vis ns
    | otherwise = ts ++ walk (n:vis) ([ n' | Fun n' _ <- ns'] ++ ns) where
        (ns',ts) = L.partition isTerminal (productions tg n)
  isTerminal Term{} = False
  isTerminal _ = True
  --       concatMap walk' (productions tg n)
  -- walk' t@(Term f _) = [t]
  -- walk' (Fun m _) = walk' (n:vis) m 
                      

insert :: (Ord f, Ord v, Ord x) => TGRule f v x -> TG f v x -> TG f v x
insert (Rule lhs rhs) = M.alter ins lhs where
  ins Nothing = Just [rhs]
  ins (Just rhss) = Just (rhs:rhss)

member :: (Ord f, Ord v, Ord x) => TGRule f v x -> TG f v x ->  Bool
member (Rule lhs rhs) = maybe False (rhs `elem`) . M.lookup lhs

rules :: TG f v x -> [TGRule f v x]
rules tg = [ Rule lhs rhs | (lhs,rhss) <- M.toList tg, rhs <- rhss ]

fromRules :: (Ord f, Ord v, Ord x) => [TGRule f v x] -> TG f v x
fromRules = foldl (flip insert) M.empty

startSymbol :: TGSym f v x
startSymbol = R 0

auxSymbol :: x -> TGSym f v x
auxSymbol = X

terminal :: TGSym f v x -> TGTerm f v x
terminal f = Fun f []

fun :: f -> [TGTerm f v x] -> TGTerm f v x
fun f = Fun (F f)


liftTerm :: Int -> Term f v -> TGTerm f v x 
liftTerm i (Var v) = Substitution v i
liftTerm i (Fun f ts) = Term f (map (liftTerm i) ts)

unlift :: TGTerm f v x -> Term f ()
unlift (Term f ts) = Fun f (map unlift ts)
unlift _ = Var ()

newtype Match f v x = Match [(TGSym f v x,TGTerm f v x)] deriving Show
data Matches f v x =
  Matches { matchedRule :: (R.Rule f v, Int)
          , matches :: [Match f v x] }
  deriving Show

minimalMatches :: (Ord x, Ord v, Ord f) => TG f v x -> TGTerm f v x -> (R.Rule f v, Int) -> Matches f v x
minimalMatches tg s (rl@(R.Rule lhs _), i) =
     Matches { matchedRule = (rl, i)
             , matches = map Match (minMatches lhs s)}
  where
    minMatches (Var v) u = return [(V v i, u)]
    minMatches (Fun f ls) (Term g vs)
      | f /= g    = mzero
      | otherwise = concat <$> sequence [minMatches li vi | (li,vi) <- zip ls vs]
    minMatches t u@(Fun f _)
      = msum [ minMatches t r | r <- productions' tg f]
    minMatches _ _ = mzero
      
-- complete :: (Ord x, Ord f, Ord v) => [(R.Rule f v, Int)] -> TG f v x -> TG f v x
complete prog = exec (fixM makeClosure) where

  exec m = execState (execStateT (execStateT m S.empty) True)
  setModified = lift . modify . const

  currentTG = lift (lift get)

  extend = mapM_ insertTG where
    insertTG rl@(Rule lhs rhs)
      | terminal lhs == rhs = return ()
      | otherwise = do
          isElt <- member rl <$> lift (lift get)
          unless isElt $ do
            tracePretty (lhs,"->",rhs) (return ())
            lift (lift (modify (insert rl)))
            setModified True

  fixM op = do
    setModified False
    (rules <$> currentTG) >>= mapM_ op
    modified <- lift get 
    when modified (fixM op)

  makeClosure (Rule lhs rhs) = do
    tg <- currentTG
    mapM_ (closeSubterm tg) (contexts rhs)
    where
      closeSubterm tg (ctx,t@(Term _ args)) = do 
        argNormalised <- andM [ not <$> reducible ai | ai <- args]
        let
          ms = map (minimalMatches tg t) prog
          closeWithMatch match
            | null (matches match) = return ()
            | otherwise = do
                let (rl,i) = matchedRule match
                extend [ lhs --> (ctx `C.apply` (Result i))
                       , R i --> liftTerm i (R.rhs rl)]
                extend [ v --> e
                       | Match m <- matches match, (v,e) <- m ]
              where
        when argNormalised (mapM_ closeWithMatch ms)
        
      closeSubterm _ _ = return ()

  -- hasRedex s == all terms represented by s are reducible
  reducible s = withMemoR reducible1 s
    where
      withMemoR m t = do
        withNF <- get
        if t `S.member` withNF
          then return False
          else do
          red <- m t
          unless red (modify (S.insert t))
          return red

      reducible1 (Result r) = do
        tg <- currentTG
        andM [ withMemoR reducible2 rhs | rhs <- productions tg (R r) ]
      reducible1 e = reducible2 e

      reducible2 r@(Term _ rs) = do
        tg <- currentTG
        ra <- orM [ withMemoR reducible2 ri | ri <- rs ]
        return (ra || any (not . null . matches . minimalMatches tg r) prog)
      reducible2 _ = return False
      
  
orM :: Monad m => [m Bool] -> m Bool
orM [] = return False
orM (mb:ms) = do {b <- mb; if b then return b else orM ms}
      
andM :: Monad m => [m Bool] -> m Bool
andM [] = return True
andM (mb:ms) = do {b <- mb; if b then andM ms else return False}
      
-- refinements :: (Ord f, Ord v, Ord x) => [R.Rule f v] -> TG f v x -> R.Rule f v -> (v -> Bool) ->  [R.Rule f Int]
refinements prog initial = 
  \ rl@(R.Rule lhs rhs) refineP ->
   case L.lookup rl prog' of
    Nothing -> []
    Just i
      | ruleReachable -> [R.Rule (s `apply` lhs) (s `apply` rhs) | s <- substs]
      | otherwise -> []
      where
        apply s t = fromJust (S.gApply s t)
        substs = map toSubst (foldl (\ l v -> [ (v,p):s | s <- l, p <- patterns v]) [[]] (L.nub (R.vars rl))) where 
          patterns v
            | refineP v = L.nub (map unlift (reducts (V v i)))
            | otherwise = [T.Var ()]
        ruleReachable = not (null (productions tg (R i)))
  where
    prog' = zip prog [1..]
    
    tg = let tg' = complete prog' initial in tracePretty (M.toList tg') tg'

    reducts s =
      case productions' tg s of 
       [] -> [Fun s []]
       rhss -> rhss
      -- if null rhss then [s] else rhss
      -- where rhss = [rhs | R.Rule lhs rhs <- rs, lhs == s]

    toSubst = ST.fromMap . M.fromList . runVarSupply . mapM (\ (v,p) -> (,) v <$> ren p)
      where
        ren (T.Fun f ts) = T.Fun f <$> mapM ren ts
        ren _            = T.Var <$> fresh


        


