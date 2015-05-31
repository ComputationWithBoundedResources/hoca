module Hoca.PCF.Sugar.Pretty where

import           Hoca.PCF.Sugar.Types
import           Hoca.Utils (ppSeq)

import qualified Text.PrettyPrint.ANSI.Leijen as PP

instance PP.Pretty Symbol where
  pretty (Symbol s) = PP.text s
  
instance PP.Pretty Variable where
  pretty (Variable v) = PP.text v


prettyTyCon :: (PP.Pretty t, PP.Pretty v) => t -> [v] -> PP.Doc
prettyTyCon n [] = PP.pretty n
prettyTyCon n [t] = PP.pretty t PP.<+> PP.pretty n
prettyTyCon n ts = PP.parens (ppSeq PP.comma [PP.pretty t | t <- ts]) PP.<+> PP.pretty n

instance PP.Pretty TypeName where
  pretty (TypeName n) = PP.text n

instance PP.Pretty TypeVar where
  pretty (TypeVar v) = PP.text "'" PP.<> PP.text v

instance PP.Pretty Type where
  pretty t = pp t False where
    pp (TyVar v) _ = PP.pretty v
    pp (TyCon n ts) _ = prettyTyCon n ts
    pp (t1 :~> t2) a = maybeParens (pp t1 True PP.<+> PP.text "->" PP.<+> pp t2 False) where
      maybeParens
        | a = PP.parens
        | otherwise = id

instance PP.Pretty TypeDecl where
  pretty (TypeDecl tn vs cs) =
    PP.text "type" PP.<+> prettyTyCon tn vs
    PP.<+> PP.text "="
    PP.<+> ppSeq (PP.text "|") [ppCon c as | (c,as) <- cs] where
      ppCon c as =
        PP.pretty c PP.<+> PP.text "of"
        PP.<+> ppSeq (PP.text "*") [PP.pretty a | a <- as]

prettyLet :: String -> [(Pos, Variable, [Variable], Exp)] -> Exp -> PP.Doc
prettyLet n ls e =
  PP.vcat [ PP.text m PP.<+> PP.hsep (map PP.pretty (v:vs)) PP.<+> PP.text "=" PP.<+> PP.pretty ei
          | (m,(_,v,vs,ei)) <- zip (n : repeat "and") ls]
  PP.<$> PP.text "in" PP.<+> PP.indent 0 (PP.pretty e)

prettyCon :: Symbol -> [PP.Doc] -> PP.Doc
prettyCon f ds = PP.pretty f PP.<> PP.encloseSep PP.lparen PP.rparen PP.comma ds

instance PP.Pretty Exp where
  pretty (Abs _ v e) = PP.parens (PP.text "fun" PP.<+> PP.pretty v PP.<+> PP.text "->" PP.<+> PP.pretty e)
  pretty (Var _ v) = PP.pretty v
  pretty (Err _) = PP.text "error"
  pretty (Con _ f as) = prettyCon f (map PP.pretty as)
    
  pretty (App _ e1 e2) = PP.parens (PP.pretty e1 PP.<+> PP.pretty e2)
  pretty (Lazy _ e) = PP.text "lazy" PP.<+> PP.parens (PP.pretty e)
  pretty (Force _ e) = PP.text "force" PP.<+> PP.parens (PP.pretty e)    
  pretty (Cond _ e cs) =
    PP.parens (PP.text "match" PP.<+> PP.pretty e PP.<+> PP.text "with"
               PP.<$> PP.vsep [ PP.text "|" PP.<+> prettyCon g (map PP.pretty vs)
                                PP.<+> PP.text "->" PP.<+> PP.indent 2 (PP.pretty e')
                              | (g,vs,e',_) <- cs ])
  pretty (Let _ ls e) = prettyLet "let" ls e
  pretty (LetRec _ ls e) = prettyLet "let rec" ls e


prettyLetPP :: Variable -> [Variable] -> Exp -> [ProgramPoint] -> PP.Doc
prettyLetPP f vs e ps = 
  PP.text "In the definition 'let" 
  PP.<+> (ppSeq PP.space [PP.pretty vi | vi <- f:vs]
               PP.<+> PP.text "= ...', namely")
  PP.<$> PP.pretty e
  PP.<$$> PP.pretty (Context (filter nf ps))
      where nf (LetBdy g _ _) = f /= g
            nf (LetRecBdy g _ _) = f /= g
            nf _ = True
  

instance PP.Pretty Context where 
  pretty (Context (LetBdy f vs e:ps)) = prettyLetPP f vs e ps
  pretty (Context (LetRecBdy f vs e:ps)) = prettyLetPP f vs e ps
  pretty (Context (CaseGuard e:ps)) = 
      PP.text "In a matched expression, namely"
      PP.<$> PP.indent 2 (PP.pretty e)
      PP.<$$> PP.pretty (Context ps)
  pretty (Context (CaseBdy _ [] e:ps)) = 
      PP.text "In the case of a match-expression, namely"
      PP.<$> PP.indent 2 (PP.pretty e)
      PP.<$$> PP.pretty (Context ps)                       
  pretty (Context (ConstructorArg i e:ps)) = 
      PP.text "In the" PP.<+> PP.int i PP.<> PP.text"th argument of a constructor, namely"    
      PP.<$> PP.indent 2 (PP.pretty e)
      PP.<$$> PP.pretty (Context ps)      
  pretty (Context (Lapp e:ps)) = 
      PP.text "In the left argument of an application, namely"    
      PP.<$> PP.indent 2 (PP.pretty e)
      PP.<$$> PP.indent 2 (PP.pretty (Context ps))
  pretty (Context (Rapp e:ps)) = 
      PP.text "In the left argument of an application, namely"    
      PP.<$> PP.indent 2 (PP.pretty e)
      PP.<$$> PP.pretty (Context ps)
  pretty (Context (_:ps)) = PP.pretty (Context ps)
  pretty (Context []) = PP.empty

