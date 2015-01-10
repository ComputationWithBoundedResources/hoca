-- | 

module Hoca.TreeGrammar (
  Term (..)
  , Production (..)
  , Grammar
  , toMap
  , fromList
  , toList
  , insert
  , member
  , produces
  , produces'
  , nonTerminals
  ) where

import qualified Data.Map as M
import qualified Data.List as L
import Data.Maybe (fromMaybe)
import qualified Text.PrettyPrint.ANSI.Leijen as PP

data Term t n = Terminal t [Term t n]
              | NonTerminal n
              deriving (Eq,Ord,Show)
                       
newtype Grammar t n = G { toMap :: M.Map n [Term t n] }
                    deriving (Show)
                               
data Production t n = Production n (Term t n)
                      deriving (Show)

nonTerminalsDL :: Term t n -> [n] -> [n]
nonTerminalsDL (NonTerminal n) = (:) n
nonTerminalsDL (Terminal _ ts) = foldl (\ f ti -> f . nonTerminalsDL ti) id ts

nonTerminals :: Term t n -> [n]
nonTerminals t = nonTerminalsDL t []

instance (PP.Pretty t, PP.Pretty n) => PP.Pretty (Term t n) where
    pretty (NonTerminal n) = PP.pretty n
    pretty (Terminal t ts) = PP.pretty t PP.<> args where
      args = PP.encloseSep PP.lparen PP.rparen PP.comma [PP.pretty ti | ti <- ts]

instance (PP.Pretty t, PP.Pretty n) => PP.Pretty (Production t n) where
    pretty (Production n m) = PP.pretty n PP.<+> PP.text "->" PP.<+> PP.pretty m

instance (PP.Pretty t, PP.Pretty n) => PP.Pretty (Grammar t n) where
    pretty (G m) = PP.encloseSep PP.lbrace PP.rbrace PP.comma [ pp n ts | (n,ts) <- M.toList m] where
      pp _ [] = PP.empty
      pp n (t:ts) =
        PP.pretty n PP.<+> PP.align (PP.vsep (PP.text "->" PP.<+> PP.pretty t
                                              : [PP.text "| " PP.<+> PP.pretty ti | ti <- ts]))

produces :: (Ord n) => Grammar t n -> n -> [Term t n]
produces tg lhs = fromMaybe [] (M.lookup lhs (toMap tg))

produces' :: (Ord n) => Grammar t n -> n -> [Term t n]
produces' tg lhs = walk [] [lhs] where
  walk _ [] = []
  walk vis (n:ns)
    | n `elem` vis = walk vis ns
    | otherwise = ts ++ walk (n:vis) ([ m | NonTerminal m <- ms] ++ ns) where
        (ts,ms) = L.partition isTerminal (produces tg n)
  isTerminal Terminal {} = True
  isTerminal _ = False


insert :: Ord n => Production t n -> Grammar t n -> Grammar t n
-- insert (Production lhs (NonTerminal rhs)) g | lhs == rhs = g
insert (Production lhs rhs) (G m) = G (M.alter ins lhs m) where
  ins Nothing = Just [rhs]
  ins (Just rhss) = Just (rhs:rhss)

member :: (Ord n, Eq t) => Production t n -> Grammar t n -> Bool
-- member (Production lhs (NonTerminal rhs)) | lhs == rhs = const True
member (Production lhs rhs) = maybe False (rhs `elem`) . M.lookup lhs . toMap

toList :: Grammar t n -> [Production t n]
toList (G m) = [ Production lhs rhs | (lhs,rhss) <- M.toList m, rhs <- rhss ]

fromList :: Ord n => [Production t n] -> Grammar t n
fromList = foldl (flip insert) (G M.empty)


