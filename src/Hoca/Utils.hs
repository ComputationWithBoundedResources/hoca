-- | 

module Hoca.Utils where

import qualified Data.Rewriting.Term as T
import qualified Data.Rewriting.Context as C
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Debug.Trace (trace)
import Control.Monad.State (MonadState,State,StateT,evalState,evalStateT,get,modify)
import Data.Monoid (Monoid(..))
import Control.Monad ((>=>))
import qualified Data.Rewriting.Rule as R


orM :: Monad m => [m Bool] -> m Bool
orM [] = return False
orM (mb:ms) = do {b <- mb; if b then return b else orM ms}
      
andM :: Monad m => [m Bool] -> m Bool
andM [] = return True
andM (mb:ms) = do {b <- mb; if b then andM ms else return False}

composeM :: Monad m => [a -> m a] -> a -> m a 
composeM = foldr (>=>) return

prod :: [[a]] -> [[a]]
prod [] = [[]]
prod (as:ass) = [ ai:asi | ai <- as, asi <- prod ass ]

-- | @(C,s) `elem` contexts t@ if and only if @t = C[s]@.
contexts :: T.Term f v -> [(C.Ctxt f v, T.Term f v)]
contexts = walk id
  where
    walk c s@(T.Var _) = [(c C.Hole,s)]
    walk c s@(T.Fun f ss) =
      (c C.Hole, s) : concatMap (\ (ls,si,rs) -> walk (\ ctxt -> c (C.Ctxt f ls ctxt rs)) si) (parts [] ss)

    parts _ [] = []
    parts ls (t:rs) = (ls,t,rs) : parts (ls ++ [t]) rs

fresh :: MonadState Int m => m Int
fresh = modify succ >> get

runVarSupplyT :: Monad m => StateT Int m a -> m a
runVarSupplyT = flip evalStateT 0

runVarSupply :: State Int a -> a
runVarSupply = flip evalState 0


tracePretty :: PP.Pretty e => e -> a -> a
tracePretty e = trace (render (PP.pretty e) "")
  where render = PP.displayS . PP.renderSmart 1.0 80

tracePretty' :: PP.Pretty a => a -> a
tracePretty' e = tracePretty e e 


insertInto :: (t -> t -> Bool) -> [t] -> t -> [t]
insertInto _ [] b = [b]
insertInto isInstanceOf (a:as) b
  | a `isInstanceOf` b = insertInto isInstanceOf as b
  | b `isInstanceOf` a = a:as
  | otherwise = a : insertInto isInstanceOf as b

-- avoid redundant rules, i.e. those that are instances of other rules
newtype RS f v = RS [R.Rule f v]

instance (Eq f, Ord v) => Monoid (RS f v) where
  mempty = RS []
  mappend (RS rs1) (RS rs2) = RS (foldl (insertInto R.isInstanceOf) rs1 rs2)

rsFromList :: (Ord v, Eq f) => [R.Rule f v] -> RS f v 
rsFromList rs = RS (foldl (insertInto R.isInstanceOf) [] rs)

rsToList :: RS f v -> [R.Rule f v]
rsToList (RS l) = l

nubRules :: (Eq f, Ord v) => [R.Rule f v] -> [R.Rule f v]
nubRules = rsToList . rsFromList

-- termset, implicitly closed under instances

newtype TS f v = TS [T.Term f v]

instance (Eq f, Ord v) => Monoid (TS f v) where
  mempty = TS []
  mappend (TS rs1) (TS rs2) = TS (foldl (insertInto T.isInstanceOf) rs1 rs2)

tsFromList :: (Ord v, Eq f) => [T.Term f v] -> TS f v 
tsFromList ts = TS (foldl (insertInto T.isInstanceOf) [] ts)

tsToList :: TS f v -> [T.Term f v]
tsToList (TS l) = l

putDocLn :: PP.Pretty e => e -> IO ()
putDocLn = putStrLn . render

render :: PP.Pretty e => e -> String
render d = PP.displayS (PP.renderSmart 1.0 80 (PP.pretty d)) ""

writeDocFile :: PP.Pretty e => FilePath -> e -> IO ()
writeDocFile fn = writeFile fn . render

($$) :: PP.Doc -> PP.Doc -> PP.Doc
pa $$ pb = PP.align (pa PP.<$> PP.indent 1 pb)

(//) :: PP.Doc -> PP.Doc -> PP.Doc
pa // pb = PP.align (pa PP.</> pb)

ppSeq :: PP.Doc -> [PP.Doc] -> PP.Doc
ppSeq _ [] = PP.empty
ppSeq _ [a] = a
ppSeq s (a:as) = PP.align (a PP.<//> PP.cat [s PP.<> a' | a' <- as])

