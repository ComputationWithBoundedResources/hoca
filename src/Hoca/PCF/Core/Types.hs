{-# LANGUAGE OverlappingInstances #-}

module Hoca.PCF.Core.Types where

import qualified Text.PrettyPrint.ANSI.Leijen as PP
import qualified Data.IntMap as IntMap
import Data.Map (Map)
import qualified Data.Map as Map
import           Hoca.Utils (($$), (//), ppSeq)
import           Data.List (nub)

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

instance PP.Pretty (TypedExp l) where
  pretty (Var _ i) = PP.underline (PP.int i)
  pretty (Con _ f as) =
    PP.pretty f PP.<> PP.tupled [PP.pretty ai | ai <- as]
  pretty (Bot _) = PP.bold (PP.text "_|_")
  pretty (Abs (_,t) n e) = PP.align (PP.nest 2 (PP.parens (PP.bold (PP.text "λ" PP.<> pp n) PP.<+> PP.text ":" PP.<+> PP.pretty t PP.<> PP.text "." PP.</> PP.pretty e)))
    where pp (Just name) = PP.text name
          pp Nothing = PP.empty
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
-- Types
----------------------------------------------------------------------

type TypeVariable = Int
type TypeName = String

data Type = TyVar TypeVariable
          | TyCon TypeName [Type]
          | Type :-> Type deriving (Eq)

data TypeSchema = FVar TypeVariable
                | BVar TypeVariable
                | TSCon TypeName [TypeSchema] 
                | TypeSchema :~> TypeSchema  deriving (Eq)

type TSignature = Map Symbol ([TypeSchema],TypeSchema)

type TypedExp l = Exp (l,Type)

typeOf :: TypedExp l -> Type
typeOf = snd . label

tsMatrix :: TypeSchema -> Type
tsMatrix (FVar i) = TyVar i
tsMatrix (BVar i) = TyVar i
tsMatrix (TSCon n ts) = TyCon n (map tsMatrix ts)
tsMatrix (t1 :~> t2) = tsMatrix t1 :-> tsMatrix t2

-- prettyprinting
variableNames :: [String]
variableNames = [ [c] | c <- ['a'..'z']] ++ [ 'a' : show i | i <- [(1 :: Int)..] ]

prettyTyCon :: (PP.Pretty t, PP.Pretty v) => t -> [v] -> PP.Doc
prettyTyCon n [] = PP.pretty n
prettyTyCon n [t] = PP.pretty t PP.<+> PP.pretty n
prettyTyCon n ts = PP.parens (ppSeq PP.comma [PP.pretty t | t <- ts]) PP.<+> PP.pretty n

prettyTyVar :: TypeVariable -> PP.Doc
prettyTyVar v = PP.text ("'" ++ variableNames !! v)


instance PP.Pretty TypeSchema where
  pretty t = ppBVars (nub (btvs t)) PP.<> PP.text "." PP.<+> PP.pretty (tsMatrix t) where
    btvs (FVar _) = []
    btvs (BVar m) = [m]
    btvs (TSCon _ tts) = concatMap btvs tts
    btvs (t1 :~> t2) = btvs t1 ++ btvs t2
    ppBVars [] = PP.empty
    ppBVars bvs = PP.text "forall" PP.<+> ppSeq PP.space [ prettyTyVar v | v <- bvs ]



instance PP.Pretty Type where 
  pretty t = ppType t False where
    ppType (TyVar i) _ = prettyTyVar i
    ppType (TyCon n ts) _ = prettyTyCon n ts
    ppType (t1 :-> t2) a = maybeParens (ppType t1 True PP.<+> PP.text "->" PP.<+> ppType t2 False) where
      maybeParens
        | a = PP.parens
        | otherwise = id
         

instance PP.Pretty TSignature where 
    pretty ts = 
        PP.vcat [ PP.pretty ci PP.<+> PP.text "::" PP.<+> ppTSig tins tout
                | (ci, (tins,tout)) <- Map.toList ts ] where
    
        ppTpe (tsMatrix -> t@(_ :-> _)) = PP.parens (PP.pretty t)
        ppTpe (tsMatrix -> t) = PP.pretty t
        ppTSig [] tout = ppTpe tout
        ppTSig tins tout = 
            PP.align (ppSeq (PP.text " * ") (ppTpe `map` tins)
                      PP.<+> PP.text "->" PP.<+> ppTpe tout)
                

----------------------------------------------------------------------
-- Program
----------------------------------------------------------------------

data Program l = 
     Program { signature :: TSignature
             , expression :: Exp l }

instance PP.Pretty (Program l) where 
    pretty p = PP.pretty (expression p)
        
type TypedProgram l = Program (l,Type)

instance PP.Pretty (TypedProgram l) where 
    pretty p = 
        PP.pretty e 
        PP.<+> PP.text ":" PP.<+> PP.pretty (typeOf e)
        PP.<$> PP.text "where" 
        PP.<$> PP.nest 2 (PP.align (PP.pretty (signature p)))
        where e = expression p
