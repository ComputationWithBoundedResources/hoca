module Hoca.Strategy
       (
         Choice (..)
       , (:=>)
       , run
       , Result (..) -- TODO: remove
       , succeeded
       , try
       , abort
       , (>=>)
       , (<=>)
       , repeated
       , exhaustive
       , sequenceS
       , provided
       , alt
       , choice
       , withInput
       , traced
       , logMsg
       )
       where

import Control.Applicative (Alternative(..))
import Hoca.Utils(tracePretty, composeM)
import qualified Control.Monad
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Control.Monad (guard, MonadPlus(..), ap)


data Result a =
  Fail
  | Success [a]
  deriving (Show)

instance Functor Result where
  fmap _ Fail = Fail
  fmap f (Success as) = Success (map f as)
  

instance Monad Result where
  return i = Success [i]
  Fail >>= _ = Fail
  Success as >>= f =
    case concat [ bs | Success bs <- map f as ] of
     [] -> Fail
     bss -> Success bss

instance MonadFail Result where
  fail _ = Fail

instance Applicative Result where
  pure = return
  (<*>) = ap

succeeded :: Result a -> Bool
succeeded Fail = False
succeeded Success {} = True

instance Alternative Result where
  empty = Fail
  Fail <|> rb = rb
  ra <|> Fail = ra
  Success as <|> Success bs = Success (as ++ bs)

instance MonadPlus Result where
  mzero = empty
  mplus = (<|>)

class Choice m where
  (<||>) :: m a -> m a -> m a
           
instance Choice Maybe where
  (<||>) = (<|>)

instance Choice Result where
  Fail <||> rb = rb
  ra <||> _ = ra

-- strategies

type a :=> b = a -> Result b


run :: a :=> b -> a -> Maybe b
run s a =
  case s a of
   Fail -> Nothing
   Success (r:_) -> Just r
   Success _ -> error "strategy returned empty result"

try :: a :=> a -> a :=> a
try m = m <=> pure 

(<=>) :: a :=> b -> a :=> b -> a :=> b
(<=>) f1 f2 a = f1 a <||> f2 a

alt :: [a :=> b] -> a :=> b
alt = foldl (<=>) abort

(<+>) :: a :=> b -> a :=> b -> a :=> b
(<+>) f1 f2 a = f1 a <|> f2 a

choice :: [a :=> b] -> a :=> b
choice = foldl (<+>) abort

abort :: a :=> b
abort _ = empty


(>=>) :: a :=> b -> b :=> c -> a :=> c
(>=>) = (Control.Monad.>=>)

sequenceS :: [a :=> a] -> a :=> a
sequenceS = composeM


repeated :: Int -> a :=> a -> a :=> a
repeated n m
  | n <= 0 = return
  | otherwise = try (m >=> repeated (n-1) m)

exhaustive :: a :=> a -> a :=> a
exhaustive rel = rel >=> try (exhaustive rel) 

withInput :: (a -> a :=> b) -> a :=> b
withInput s a = s a a

provided :: a :=> b -> (a -> b -> Bool) -> a :=> b
provided t f p = do
  p' <- t p
  guard (f p p')
  return p'

traced :: (PP.Pretty a) => String -> a :=> a
traced s a = tracePretty doc (return a) where
  ln c = PP.text (replicate 80 c)
  doc =
    PP.text s
    PP.<$> ln '-'
    PP.<$> PP.indent 2 (PP.pretty a)
    PP.<$> ln '='
    PP.<$> PP.text ""

logMsg :: String -> a :=> a
logMsg msg a = tracePretty (PP.text msg) (return a)
