module Hoca.Strategy
       (
         Strategy (..)
       , try
       , (>=>)
       , (<=>)
       , repeated
       , exhaustive
       , traced
       )
       where

import Control.Applicative (Alternative(..), Applicative(..))
import Control.Monad ((>=>))
import Hoca.Utils(tracePretty)
import qualified Text.PrettyPrint.ANSI.Leijen as PP


class (Alternative m, Monad m) => Strategy m where
  -- | left biased choice
  (<||>) :: m a -> m a -> m a 

instance Strategy Maybe where
  Nothing <||> a = a
  Just a <||> _ = Just a  

instance Strategy [] where
  [] <||> l2 = l2
  l1 <||> _  = l1


-- combinators
try :: (Strategy m) => (a -> m a) -> a -> m a
try m a = m a <||> return a

(<=>) :: (Strategy m) => (a -> m b) -> (a -> m b) -> a -> m b
(<=>) f1 f2 a = f1 a <||> f2 a

repeated :: (Strategy m) => Int -> (a -> m a) -> a -> m a
repeated n m
  | n <= 0 = return
  | otherwise = try (m >=> repeated (n-1) m)

exhaustive :: Strategy m => (a -> m a) -> a -> m a
exhaustive rel = try (rel >=> exhaustive rel) 

traced :: (PP.Pretty a, Applicative m) => String -> a -> m a
traced s a = tracePretty doc (pure a) where
  ln c = PP.text (replicate 80 c)
  doc =
    PP.text s
    PP.<$> ln '-'
    PP.<$> PP.indent 2 (PP.pretty a)
    PP.<$> ln '='
    PP.<$> PP.text ""
