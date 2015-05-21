-- | Usable Replacement Maps for applicative rules

module Hoca.URM (
  URM
  , empty
  , usable
  , fromRules
  , urm
  , filterTerm
  ) where

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe (fromMaybe)
import Data.Rewriting.Applicative.Term
import Data.Rewriting.Applicative.Rule hiding (map)
import Data.Rewriting.Applicative.Rules (lhss, rhss)
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Control.Monad.Writer (execWriter, tell)

newtype URM f = URM (Map f [Int])

empty :: URM f
empty = URM Map.empty

usable :: Ord f => URM f -> f -> [Int]
usable (URM m) f = fromMaybe [] (Map.lookup f m)

insert :: Ord f => URM f -> f -> Int -> URM f
insert (URM m) f i = URM (Map.alter ins f m) where
  ins Nothing = Just [i]
  ins (Just us) = Just (add us)
  add [] = [i]
  add us@(j:js)
    | i < j     = i : us
    | i == j    = us
    | otherwise = j : add js

fromList :: Ord f => [(f,Int)] -> URM f
fromList = foldl (uncurry . insert) empty

urm :: Ord f => [ARule f v] -> [ATerm f v] -> URM f
urm rs calls = fromList (execWriter (mapM upos calls)) where
  upos (aterm -> t1 :@ t2) = upos t1 >> upos t2 >> return True
  upos (aterm -> Fun f ts) = do
    reds <- mapM upos ts
    tell [(f,i) | (i,True) <- zip [0..] reds]
    return (or reds || f `elem` ds)
  upos _ = return False
  ds = [f | Fun f _ <- map aterm (lhss rs)]

-- ^ approximation of usable replacement maps without unification, looking at roots only
fromRules :: Ord f => [ARule f v] -> URM f
fromRules rs = urm rs (rhss rs) where

-- ^ removes non-usable positions from applicative terms  
filterTerm :: Ord f => URM f -> ATerm f v -> ATerm f v
filterTerm _ (aterm -> Var v) =  var v
filterTerm u (aterm -> t1 :@ t2) = filterTerm u t1 `app` filterTerm u t2
filterTerm u (aterm -> Fun f ts) = fun f [ti | (i,ti) <- zip [0..] ts, i `elem` uargs]
  where uargs = usable u f
filterTerm _ _ = error "Hoca.URM.filterTerm pattern match failure"

instance PP.Pretty f => PP.Pretty (URM f) where
  pretty (URM m)
    | null l = PP.text "{}"
    | otherwise = PP.vsep [ PP.text "mu" PP.<> PP.parens (PP.pretty f)
                            PP.<+> PP.text "="
                            PP.<+> ppSet [PP.int i | i <- us]
                          | (f,us) <- l]
    where
      l = Map.toList m
      ppSet = PP.encloseSep PP.lbrace PP.rbrace PP.comma
  
