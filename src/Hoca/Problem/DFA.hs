module Hoca.Problem.DFA (
  NonTerminal (..)
  , DFAProduction
  , DFAGrammar
  , complete
  , dfa
  , unliftTerm
  ) where

import           Control.Monad (MonadPlus (..), msum, when, unless)
import           Control.Monad.State.Lazy (execState, execStateT, get, modify)
import           Control.Monad.Trans (lift)
import qualified Data.Rewriting.Applicative.Rule as R
import           Data.Rewriting.Applicative.Term (Term (..), ASym (..))
import qualified Data.Set as S
import qualified Hoca.Data.TreeGrammar as TG
import           Hoca.Problem.Type
import           Hoca.Problem.Ops
import           Hoca.Utils (andM, orM)
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Hoca.Data.MLTypes

data NonTerminal v x = X x | V v Int | R Int deriving (Ord, Eq, Show)

type DFAProduction f v x = TG.Production (ASym f) (NonTerminal v x)
type DFAGrammar f v x = TG.Grammar (ASym f) (NonTerminal v x)

instance (PP.Pretty x, PP.Pretty v) => PP.Pretty (NonTerminal x v) where
  pretty (X s) = PP.text "X" PP.<> PP.braces (PP.pretty s)
  pretty (V s i) = PP.text "V" PP.<> PP.braces (PP.text "x" PP.<> PP.pretty s PP.<> PP.text "_" PP.<> PP.int i) 
  pretty (R i) = PP.text "R" PP.<> PP.braces (PP.int i)
  
startNonTerminal :: NonTerminal v x
startNonTerminal = R 0

auxNonTerminal :: x -> NonTerminal v x
auxNonTerminal = X

liftTerm :: Int -> Term f v -> TG.Term f (NonTerminal v x)
liftTerm i (Var v) = TG.NonTerminal (V v i)
liftTerm i (Fun f ts) = TG.Terminal f (map (liftTerm i) ts)

unliftTerm :: TG.Term f (NonTerminal v x) -> Term f ()
unliftTerm (TG.Terminal f ts) = Fun f (map unliftTerm ts)
unliftTerm _ = Var ()               


type Ctxt t n = TG.Term t n -> TG.Term t n

contexts :: TG.Term t n -> [(Ctxt t n, TG.Term t n)]
contexts = walk id
  where
    walk c n@TG.NonTerminal{} = [(c,n)]
    walk c t@(TG.Terminal f ts) =
      (c, t) : concatMap (\ (ls,ti,rs) ->
                           walk (\ t' -> c(TG.Terminal f (ls ++ [t'] ++ rs))) ti)
                 (parts [] ts)

    parts _ [] = []
    parts ls (t:rs) = (ls,t,rs) : parts (ls ++ [t]) rs

newtype Match f v x = Match [DFAProduction f v x] deriving Show

data Matches f v x =
  Matches { matchedRule :: (R.ARule f v, Int)
          , matches :: [Match f v x] }
  deriving Show

minimalMatches :: (Ord f, Ord x, Ord v) => DFAGrammar f v x -> TG.Term (ASym f) (NonTerminal v x) -> (Int,TRule f v) -> Matches f v x
minimalMatches tg s (i, trl) =
     Matches { matchedRule = (rl, i)
             , matches = map Match (minMatches (R.lhs rl) s)}
  where
    rl = theRule trl
    minMatches (Var v) u = return [TG.Production (V v i) u]
    minMatches (Fun f ls) (TG.Terminal g vs)
      | f /= g    = mzero
      | otherwise = concat <$> sequence [minMatches li vi | (li,vi) <- zip ls vs]
    minMatches t (TG.NonTerminal n)
      = msum [ minMatches t r | r <- TG.produces' tg n]

extensionOf :: (Ord f, Ord x, Ord v)
               => DFAGrammar f v x -> Problem f v -> NonTerminal v x
               -> (Ctxt (ASym f) (NonTerminal v x), TG.Term (ASym f) (NonTerminal v x))
               -> [TG.Production (ASym f) (NonTerminal v x)]
extensionOf tg prog lhs (ctx,t) =
  concatMap (mkExts . minimalMatches tg t) (rulesEnum prog) where
  mkExts match
    | null (matches match) = []
    | otherwise = 
        TG.Production lhs (ctx (TG.NonTerminal (R i)))
        : TG.Production (R i) (liftTerm i (R.rhs rl))
        : [ p | Match m <- matches match, p <- m ]
    where (rl,i) = matchedRule match

complete :: (Ord f, Ord x, Ord v) => Problem f v -> DFAGrammar f v x -> DFAGrammar f v x
complete prog = exec (fixM makeClosure) where

  exec m = execState (execStateT (execStateT m S.empty) True)
  setModified = lift . modify . const

  currentTG = lift (lift get)

  addProductions = mapM_ insertTG where
    insertTG p = do
      isElt <- TG.member p <$> currentTG
      unless isElt $ do
        lift (lift (modify (TG.insert p)))
        setModified True

  fixM op = do
    setModified False
    (TG.toList <$> currentTG) >>= mapM_ op
    modified <- lift get 
    when modified (fixM op)

  makeClosure (TG.Production lhs rhs) = do
    tg <- currentTG
    mapM_ (closeSubterm tg) (contexts rhs)
    where
      closeSubterm tg (ctx,t@(TG.Terminal _ args)) = do 
        argNormalised <- andM [ not <$> reducible ai | ai <- args]
        when argNormalised (addProductions (extensionOf tg prog lhs (ctx,t)))
      closeSubterm _ _ = return ()

  -- reducible s == all terms represented by s are reducible
  reducible (TG.NonTerminal n@(R _)) = do
    tg <- currentTG
    andM [ reducible' rhs | rhs <- TG.produces tg n ]
  reducible g = reducible' g
  
  reducible' = withMemoR red where
    red t@(TG.Terminal _ ts) = do
      tg <- currentTG
      ra <- orM [ reducible' ti | ti <- ts ]
      return (ra || any (not . null . matches . minimalMatches tg t) (rulesEnum prog))
    red _ = return False
    
    withMemoR m t = do
      withNF <- get
      if t `S.member` withNF
        then return False
        else do
        r <- m t
        unless r (modify (S.insert t))
        return r

dfa :: (Ord f, Ord v) => Problem f v -> DFAGrammar f v Type
dfa prob = complete prob initialTG where

  fun f = TG.Terminal (Sym f)
  nt = TG.NonTerminal
  (-->) = TG.Production

  -- MA: for now, do the stupid thing
  initialTG = initialUntyped
  
  initialUntyped = TG.fromList (startTG ++ dataTG) where
    fs = funs prob
    dataNT = auxNonTerminal (TyCon "*" [])
    startTG = [ startNonTerminal --> fun f (replicate ar (nt dataNT))
              | (f,ar) <- fs, f `elem` defs (startTerms prob)] 
    dataTG = [ dataNT --> fun f (replicate ar (nt dataNT))
             | (f,ar) <- fs, f `elem` constrs (startTerms prob)]
    
  -- initialTG = maybe initialUntyped initialTyped (signature prob) 
  
  -- initialUntyped = error "untyped automaton not implemented"
  
  -- initialTyped sig 
  --   | any inAdmissible decs = initialUntyped
  --   | otherwise = TG.fromList (execWriter (startRules >>= close)) where
    
  --     startRules = do 
  --       ts <- sequence 
  --             [ tell [ startNonTerminal --> fun f (ntTpe `map` tins')] >> return tins'
  --             | (f, tins, _) <- signatureToList sig
  --             , f `elem` mains prob
  --             , let tins' = [const (TyCon "*" []) `o` t | t <- tins]
  --             ]
  --       return (concat ts)
  --     close = hmn
  --     decs = [ d | d@(f,_,_) <- signatureToList sig, isConstructor f]

  --     inAdmissible (_,tins,TyCon n _) = any p tins where
  --       p (TyCon m as) = n == m && any (not . simple) as
  --       p _ = True
  --       simple (TyVar _) = True
  --       simple (_ :-> _) = False
  --       simple a = groundNF a
  --       groundNF (TyCon _ as) = all groundNF as
  --       groundNF _ = False 
        
          
