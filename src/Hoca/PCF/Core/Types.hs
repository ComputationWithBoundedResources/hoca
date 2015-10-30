module Hoca.PCF.Core.Types where

import qualified Data.IntMap as IntMap
import           Hoca.Data.MLTypes
import           Hoca.Utils (($$), (//), ppSeq)
import qualified Text.PrettyPrint.ANSI.Leijen as PP

----------------------------------------------------------------------
-- Symbols
----------------------------------------------------------------------

data Symbol = Symbol { sname :: String, sarity :: Int } deriving (Show, Eq, Ord)

symbol :: String -> Int -> Symbol
symbol = Symbol

instance PP.Pretty Symbol where
  pretty = PP.text . sname

----------------------------------------------------------------------
-- Expressions, De-Bruin style
----------------------------------------------------------------------

type Variable = Int
                
data Exp l =
  Var l Variable
  | Con l Symbol [Exp l]
  | Bot l 
  | Abs l (Maybe String) (Exp l) 
  | App l (Exp l) (Exp l)
  | Cond l (Exp l) [(Symbol, Exp l)]
  | Fix l Int [Exp l]
  deriving (Show, Eq, Ord)

label :: Exp l -> l
label (Var l _) = l
label (Con l _ _) = l
label (Bot l) = l
label (Abs l _ _) = l
label (App l _ _) = l
label (Cond l _ _) = l
label (Fix l _ _) = l 

instance Functor Exp where
  f `fmap` (Var l v) = Var (f l) v
  f `fmap` (Con l g es) = Con (f l) g (map (fmap f) es)
  f `fmap` (Bot l) = Bot (f l)
  f `fmap` (Abs l n e) = Abs (f l) n (f `fmap` e)
  f `fmap` (App l e1 e2) = App (f l) (f `fmap` e1) (f `fmap` e2)
  f `fmap` (Cond l g cs) = Cond (f l) (f `fmap` g) [(c,f `fmap` ec) | (c,ec) <- cs]  
  f `fmap` (Fix l i es) = Fix (f l) i (map (f `fmap`) es)


instance PP.Pretty (Exp l) where
  pretty (Var _ i) = PP.underline (PP.int i)
  pretty (Con _ f as) =
    PP.pretty f PP.<> PP.tupled [PP.pretty ai | ai <- as]
  pretty (Bot _) = PP.bold (PP.text "_|_")
  pretty (Abs _ n e) = PP.parens (PP.bold (PP.text "λ" PP.<> pp n) PP.<> PP.text "." // PP.pretty e)
    where pp (Just name) = PP.text name
          pp Nothing = PP.empty
  pretty (App _ e1 e2) =
    PP.parens (PP.pretty e1 // PP.pretty e2)
  pretty (Fix _ i es) =
    PP.parens (PP.bold (PP.text "fix_" PP.<> PP.int i) $$ PP.brackets (ppSeq PP.comma [ PP.pretty e | e <- es]))
  pretty (Cond _ e cs) =
    PP.parens ((PP.bold (PP.text "case") PP.<+> PP.pretty e PP.<+> PP.bold (PP.text "of"))
               $$ PP.braces (ppSeq (PP.text " | ") [ PP.pretty g PP.<+> PP.text "->" PP.<+> PP.pretty e'
                                                   | (g,e') <- cs ]))

instance {-# OVERLAPPING #-} PP.Pretty (TypedExp l) where
  pretty (Var _ i) = PP.underline (PP.int i)
  pretty (Con _ f as) =
    PP.pretty f PP.<> PP.tupled [PP.pretty ai | ai <- as]
  pretty (Bot _) = PP.bold (PP.text "_|_")
  pretty (Abs (_,t :-> _) n e) = PP.align (PP.nest 2 (PP.parens (PP.bold (PP.text "λ" PP.<> pp n) PP.<+> PP.text ":" PP.<+> PP.pretty t PP.<> PP.text "." PP.</> PP.pretty e)))
    where pp (Just name) = PP.text name
          pp Nothing = PP.empty
  pretty (Abs {}) = error "expression not well-typed"
  pretty (App _ e1 e2) =
    PP.align (PP.nest 2 (PP.parens (PP.pretty e1 PP.</> PP.pretty e2)))
  pretty (Fix _ i es) =
    PP.parens (PP.bold (PP.text "fix_" PP.<> PP.int i) $$ PP.brackets (ppSeq PP.comma [ PP.pretty e | e <- es]))
  pretty (Cond _ e cs) =
    PP.parens ((PP.bold (PP.text "case") PP.<+> PP.pretty e PP.<+> PP.bold (PP.text "of"))
               $$ PP.braces (ppSeq (PP.text "|") [ PP.pretty g PP.<+> PP.text "->" PP.<+> PP.pretty e'
                                                   | (g,e') <- cs ]))



type Subst l = IntMap.IntMap (Exp l)

----------------------------------------------------------------------
-- Program
----------------------------------------------------------------------

data Program l = 
     Program { signature :: Signature Symbol
             , expression :: Exp l }

instance PP.Pretty (Program l) where 
    pretty p = PP.pretty (expression p)


----------------------------------------------------------------------
-- Types Expressions and programs
----------------------------------------------------------------------


type TypedExp l = Exp (l,Type)

typeOf :: TypedExp l -> Type
typeOf = snd . label

        
type TypedProgram l = Program (l,Type)

instance {-# OVERLAPPING #-} PP.Pretty (TypedProgram l) where 
  pretty p =
    PP.pretty e 
    PP.<+> PP.text ":" PP.<+> PP.pretty (typeOf e)
    PP.<$> PP.text "where" 
    PP.<$> PP.nest 2 (PP.align (PP.pretty (signature p)))
    where e = expression p
