module Hoca.PCF.Core.DMInfer where

import           Control.Arrow (second)
import           Control.Monad.Except

import qualified Text.PrettyPrint.ANSI.Leijen as PP
import           Hoca.PCF.Sugar.Types (Context)
import           Hoca.PCF.Sugar.Pretty ()
import           Hoca.PCF.Core.Types
import           Hoca.Data.MLTypes


type TContext = [TypeSchema]

instance TypeTerm TContext where
  freeTV = concatMap freeTV
  boundTV = concatMap boundTV

instance Substitutable TContext where
  o s = map (o s)                                        


instance Substitutable (TypedExp l) where
  o s = fmap (second (o s))


---------------------------------------------------------------------- 
-- Type errors
---------------------------------------------------------------------- 

data TypingError l = NonUnifiable Type Type (Exp l)
                   | ConstructorNotInScope Symbol (Exp l)
                   | ExpressionNotClosed
                   | InvalidNumArguments Int Int Symbol (Exp l)

instance PP.Pretty (TypingError Context) where
    pretty (NonUnifiable t1 t2 e) = 
        PP.text "Could not match expected type" 
        PP.<+> PP.squotes (PP.pretty t2)
        PP.<+> PP.text "with actual type"
        PP.<+> PP.squotes (PP.pretty t1)
        PP.<> PP.text "."
        PP.<$$> PP.pretty (label e)
    pretty (ConstructorNotInScope f e) = 
        PP.text "The symbol" PP.<+> PP.squotes (PP.pretty f) PP.<+> PP.text "is not in scope."
        PP.<$$> PP.pretty (label e)
    pretty ExpressionNotClosed = 
        PP.text "The program contains free variables."
    pretty (InvalidNumArguments i j f e) = 
        PP.text "The symbol" PP.<+> PP.squotes (PP.pretty f) 
        PP.<+> PP.text "expects" PP.<+> PP.int i PP.<+> PP.text "arguments, but"
        PP.<+> PP.int j PP.<+> PP.text "were given."        
        PP.<$$> PP.pretty (label e)
        

---------------------------------------------------------------------- 
-- Inference Utils
---------------------------------------------------------------------- 

type DMInferM l = InferM Symbol (TypingError l)

freshForSymbol :: Exp l -> Symbol -> DMInferM l TypeDecl
freshForSymbol e f = 
  freshInstanceFor f >>= maybe (throwError err) (return . mk) where
    err = ConstructorNotInScope f e
    mk (_ ::: td) = td

unifyML :: Exp l -> [(Type,Type)] -> DMInferM l Substitution
unifyML e ts = 
    case unify ts of 
      Left (t1',t2') -> throwError (NonUnifiable t1' t2' e)
      Right s -> return s
                     
unifyM :: Exp l -> Type -> Type -> DMInferM l Substitution
unifyM e t1 t2 = unifyML e [(t1,t2)]
      

---------------------------------------------------------------------- 
-- Type inference
---------------------------------------------------------------------- 

(|-) :: TContext -> Exp l -> DMInferM l (Substitution,TypedExp l)
ctx |- Var l n 
    | n >= length ctx = throwError ExpressionNotClosed
    | otherwise = do 
  [t] <- instantiateSchemas [ctx!!n]
  return (idSubst, Var (l,t) n)
   
ctx |- e@(Con l g es) = do 
  gins :~> gout <- freshForSymbol e g
  when (length gins /= length es) $ 
       throwError (InvalidNumArguments (length gins) (length es) g e)
  (s,es') <- ctx ||- zip es gins
  return (s, Con (l, s `o` gout) g es')
  
_   |- Bot l = do 
  f <- freshVar
  return (idSubst, Bot (l,TyVar f))
  
ctx |- Abs l mn e = do 
  f <- freshVar
  (s,e') <- (fvar f : ctx) |- e
  return (s, Abs (l,s f :-> typeOf e') mn e')

ctx |- e@(App l e1 e2) = do 
  (s1,te1) <- ctx |- e1
  (s2,te2) <- (s1 `o` ctx) |- e2
  f <- freshVar
  mgu <- unifyM e (s2 `o` typeOf te1) (typeOf te2 :-> TyVar f)
  return (mgu `o` s2 `o` s1
         , App (l,mgu f) (mgu `o` s2 `o` te1) (mgu `o` te2))

ctx |- e@(Cond l g cs) = do
  (sg,g') <- ctx |- g
  n <- freshVar
  tss <- mapM (\ (ci,ei) -> (,) ei <$> freshForSymbol e ci) cs
  mgu <- unifyML e [ (typeOf g', ti) | (_,_ :~> ti) <- tss]  
  (s,es') <- sg `o` mgu `o` ctx ||- [(ei,mgu `o` foldr (:->) (TyVar n) tins) | (ei,tins :~> _) <- tss ]
  return (s `o` mgu `o` sg
         , Cond (l, s n) (s `o` mgu `o` g') (zipWith (\ (ci,_) ei' -> (ci,ei')) cs es'))   

ctx |- Fix l i es = do 
  fs <- const (TyVar <$> freshVar) `mapM` es
  let tis = [foldr (:->) fi fs  | fi <- fs ]
  (s,es') <- ctx ||- zip es tis
  return (s,Fix (l, s `o` (fs!!i)) i es')
      
(||-) :: TContext -> [(Exp l,Type)] -> DMInferM l (Substitution,[TypedExp l])      
(||-) = go idSubst [] where
    go s es _ [] = return (s,reverse es)
    go s es ctx ((e1,t1):eqs) = do 
      (s1',e1') <- ctx |- e1
      mgu <- unifyM e1 (typeOf e1') (s1' `o` t1)
      let s1 = mgu `o` s1'
      go (s1 `o` s) 
         (mgu `o` e1' : (s1 `o`) `map` es)
         (s1 `o` ctx)
         (second (s1 `o`) `map` eqs)
       
infer :: Program l -> Either (TypingError l) (TypedProgram l)
infer p = do 
  (_,te) <- runInferM (signature p) ([] |- expression p)
  return p { expression = te }
