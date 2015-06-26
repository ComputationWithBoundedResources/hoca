-- | 

module Hoca.Data.Symbol (
  -- * Symbols
   Lbl (..)
   , Name (..)
   , Symbol (..)
   , unlabeled
   , isCaseSym
   , isFixSym
   , isMainSym
   , isConstructor  
  ) where

import qualified Text.PrettyPrint.ANSI.Leijen as PP

data Lbl = LString String
         | LInt Int
         deriving (Show, Eq, Ord)
                  
newtype Name = Name [Lbl] deriving (Show, Eq, Ord, Monoid)

data Symbol =
  Con String
  | Lambda Name
  | Bot Int
  | Cond Name
  | Fix Name
  | Main
  | Labeled Int Symbol
  | Unknown Name
  deriving (Show, Eq, Ord)

instance PP.Pretty Lbl where
  pretty (LInt i) = PP.int i
  pretty (LString i) = PP.text i

instance PP.Pretty Name where
  pretty (Name []) = PP.empty
  pretty (Name [l]) = PP.pretty l
  pretty (Name (l:ls)) = PP.pretty (Name ls) PP.<> PP.text "_" PP.<> PP.pretty l

instance PP.Pretty Symbol where
  pretty (Con g) = PP.text g
  pretty (Lambda l) = PP.pretty l
  pretty (Cond l) = PP.pretty l
  pretty (Fix l) = PP.pretty l
  pretty (Bot l) = PP.text "bot" PP.<> PP.brackets (PP.pretty l)      
  pretty Main = PP.text "main"
  pretty (Labeled 0 s) = PP.pretty s
  pretty (Labeled l s) = PP.pretty s PP.<> PP.text "#" PP.<> PP.int l
  pretty (Unknown n) = PP.pretty n PP.<> PP.text "#"


unlabeled :: Symbol -> Symbol
unlabeled (Labeled _ s) = unlabeled s
unlabeled s = s

isCaseSym,isFixSym,isMainSym,isConstructor :: Symbol -> Bool
isCaseSym f = case unlabeled f of {Cond{} -> True; _ -> False }
isFixSym f = case unlabeled f of {Fix{} -> True; _ -> False }
isMainSym f = case unlabeled f of {Main{} -> True; _ -> False }
isConstructor f = case unlabeled f of {Con{} -> True; _ -> False }

