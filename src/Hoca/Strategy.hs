module Hoca.Strategy
       (
         Choice (..)
       , Strategy
       , try
       , (>=>)
       , (<=>)
       , repeated
       , exhaustive
       , sequenceS
       , traced
       )
       where

import Control.Applicative (Alternative(..))
import qualified Control.Monad as Control.Monad
import Hoca.Utils(tracePretty)
import qualified Text.PrettyPrint.ANSI.Leijen as PP


class Choice m where
  -- | left biased choice
  (<||>) :: m a -> m a -> m a 

instance Choice Maybe where
  (<||>) = (<|>)
  
instance Choice [] where
  [] <||> l2 = l2
  l1 <||> _  = l1


-- combinators

type Strategy m a b = a -> m b
  
try :: (Monad m, Choice m) => Strategy m a a -> Strategy m a a
try m a = m a <||> return a

(<=>) :: (Choice m) => Strategy m a b -> Strategy m a b -> Strategy m a b
(<=>) f1 f2 a = f1 a <||> f2 a

(>=>) :: Monad m => Strategy m a b -> Strategy m b c -> Strategy m a c
(>=>) = (Control.Monad.>=>)

repeated :: (Monad m, Choice m) => Int -> Strategy m a a -> Strategy m a a
repeated n m
  | n <= 0 = return
  | otherwise = try (m >=> repeated (n-1) m)

exhaustive :: (Monad m, Choice m) => Strategy m a a -> Strategy m a a
exhaustive rel = rel >=> try (exhaustive rel) 

sequenceS :: Monad m => [Strategy m a a] -> Strategy m a a
sequenceS = foldr (>=>) return

traced :: (PP.Pretty a, Monad m) => String -> Strategy m a a
traced s a = tracePretty doc (return a) where
  ln c = PP.text (replicate 80 c)
  doc =
    PP.text s
    PP.<$> ln '-'
    PP.<$> PP.indent 2 (PP.pretty a)
    PP.<$> ln '='
    PP.<$> PP.text ""
