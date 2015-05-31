-- | 

module Hoca.PCF.Core.DMInfer where

import qualified Data.Map as Map
import Control.Applicative
import Control.Monad.Error
import Control.Monad.RWS
import Control.Arrow (second)

import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Hoca.PCF.Sugar.Types (Context)
import Hoca.PCF.Sugar.Pretty ()
import Hoca.PCF.Core.Types

type TContext = [TypeSchema]

---------------------------------------------------------------------- 
-- Type like structures and operations
---------------------------------------------------------------------- 

class TypeTerm a where
  freeTV :: a -> [TypeVariable]
  boundTV :: a -> [TypeVariable]
  tvs :: a -> [TypeVariable]
  tvs a = freeTV a ++ boundTV a

instance TypeTerm Type where
  freeTV (TyVar m) = [m]
  freeTV (TyCon _ ts) = concatMap freeTV ts
  freeTV (t1 :-> t2) = freeTV t1 ++ freeTV t2  
  boundTV _ = []


instance TypeTerm TypeSchema where
  freeTV (FVar m) = [m]
  freeTV (BVar _) = []
  freeTV (TSCon _ tts) = concatMap freeTV tts
  freeTV (t1 :~> t2) = freeTV t1 ++ freeTV t2
  
  boundTV (FVar _) = []
  boundTV (BVar m) = [m]
  boundTV (TSCon _ tts) = concatMap boundTV tts
  boundTV (t1 :~> t2) = boundTV t1 ++ boundTV t2

instance TypeTerm TContext where
  freeTV = concatMap freeTV
  boundTV = concatMap boundTV

---------------------------------------------------------------------- 
-- Type substitutions
---------------------------------------------------------------------- 

type TSubst = Int -> Type

idSubst :: TSubst 
idSubst = TyVar 

class Substitutable a where
  o :: TSubst -> a -> a

instance Substitutable Type where  
  s `o` (TyVar m) = s m
  s `o` (TyCon n ts) = TyCon n (map (o s) ts)
  s `o` (t1 :-> t2) = (s `o` t1) :-> (s `o` t2)

instance Substitutable TypeSchema where  
  s `o` (FVar m) = fromType (s m) where
    fromType (TyVar n) = FVar n
    fromType (TyCon n ts) = TSCon n (map fromType ts)
    fromType (t1 :-> t2) = fromType t1 :~> fromType t2
  _ `o` (BVar m) = BVar m 
  s `o` (TSCon n ts) = TSCon n (map (o s) ts)
  s `o` (t1 :~> t2) = (s `o` t1) :~> (s `o` t2)
  
instance Substitutable TSubst where
  s1 `o` s2 = o s1 . s2

instance Substitutable TContext where
  o s = map (o s)                                        

instance Substitutable (TypedExp l) where
  o s = fmap (second (o s))

---------------------------------------------------------------------- 
-- Type unification
---------------------------------------------------------------------- 

unify :: [(Type,Type)] -> Either (Type,Type) TSubst
unify = go idSubst where
    go s [] = return s
    go s ((t1,t2):ups) = do 
      (s',ups') <- step t1 t2
      go (s' `o` s) (ups' ++ [(s' `o` t1', s' `o` t2') | (t1',t2') <- ups])

    step t1 t2
       | t1 == t2 = return (idSubst, [])
    step (TyVar n) t2
        | n `notElem` freeTV t2 = return (s,[]) where
         s m = if n == m then t2 else TyVar m
    step t v@(TyVar _) = step v t
    step (TyCon n1 ts1) (TyCon n2 ts2) 
        | n1 == n2 = return (idSubst, zip ts1 ts2)
    step (s1 :-> t1) (s2 :-> t2) =
        return (idSubst, [(s1,s2),(t1,t2)])
    step t1 t2 = throwError (t1,t2)

---------------------------------------------------------------------- 
-- Type inference monad
---------------------------------------------------------------------- 

data TypingError e = NonUnifiable Type Type e
                   | ConstructorNotInScope Symbol e
                   | ExpressionNotClosed
                   | InvalidNumArguments Int Int Symbol e

instance PP.Pretty (TypingError (Exp Context)) where
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
        
newtype InferM e a = InferM { runInferM :: RWST TSignature () TypeVariable (Either e) a } deriving
    ( Applicative, Functor, Monad
    , MonadReader TSignature
    , MonadState TypeVariable -- next fresh variable
    , MonadError e )

run :: TSignature -> InferM e a -> Either e a
run sig e = fst <$> evalRWST (runInferM e) sig 0

fresh :: InferM e TypeVariable
fresh = do { n <- get; modify (+1); return n }

instantiate :: [TypeSchema] -> InferM e [Type]
instantiate tts = do 
    n <- get
    modify (+ f) 
    return (map (bindTypeInst (\ b -> TyVar (b + n))) tts)
    where 
      f = 1 + maximum (0:concatMap boundTV tts)
      bindTypeInst s (BVar n) = s n
      bindTypeInst _ (FVar n) = TyVar n
      bindTypeInst s (TSCon n ts) = TyCon n (map (bindTypeInst s) ts)
      bindTypeInst s (t1 :~> t2) = bindTypeInst s t1 :-> bindTypeInst s t2

freshForSymbol :: Exp l -> Symbol -> InferM (TypingError (Exp l)) ([Type],Type)
freshForSymbol e f = 
    (Map.lookup f <$> ask) >>= maybe err inst where
        err = throwError (ConstructorNotInScope f e)
        inst (tsins,tsout) = do 
          (tout:tins) <- instantiate (tsout:tsins)
          return (tins,tout)

unifyML :: e -> [(Type,Type)] -> InferM (TypingError e) TSubst
unifyML e ts = 
    case unify ts of 
      Left (t1',t2') -> throwError (NonUnifiable t1' t2' e)
      Right s -> return s
                     
unifyM :: e -> Type -> Type -> InferM (TypingError e) TSubst
unifyM e t1 t2 = unifyML e [(t1,t2)]
      

(|-) :: TContext -> Exp l -> InferM (TypingError (Exp l)) (TSubst,TypedExp l)
ctx |- Var l n 
    | n >= length ctx = throwError ExpressionNotClosed
    | otherwise = do 
  [t] <- instantiate [ctx!!n]
  return (idSubst, Var (l,t) n)
   
ctx |- e@(Con l g es) = do 
  (gins,gout) <- freshForSymbol e g
  when (length gins /= length es) $ 
       throwError (InvalidNumArguments (length gins) (length es) g e)
  (s,es') <- ctx ||- zip es gins
  return (s, Con (l, s `o` gout) g es')
  
_   |- Bot l = do 
  f <- fresh
  return (idSubst, Bot (l,TyVar f))
  
ctx |- Abs l mn e = do 
  f <- fresh
  (s,e') <- (FVar f : ctx) |- e
  return (s, Abs (l,s f :-> typeOf e') mn e')

ctx |- e@(App l e1 e2) = do 
  (s1,te1) <- ctx |- e1
  (s2,te2) <- (s1 `o` ctx) |- e2
  f <- fresh
  mgu <- unifyM e (s2 `o` typeOf te1) (typeOf te2 :-> TyVar f)
  return (mgu `o` s2 `o` s1
         , App (l,mgu f) (mgu `o` s2 `o` te1) (mgu `o` te2))

ctx |- e@(Cond l g cs) = do
  (sg,g') <- ctx |- g
  n <- fresh
  tss <- mapM (\ (ci,ei) -> (,) ei <$> freshForSymbol e ci) cs
  mgu <- unifyML e [ (typeOf g', ti) | (_,(_,ti)) <- tss]  
  (s,es') <- sg `o` mgu `o` ctx ||- [(ei,mgu `o` foldr (:->) (TyVar n) tins) | (ei,(tins,_)) <- tss ]
  return (s `o` mgu `o` sg
         , Cond (l, s n) (s `o` mgu `o` g') (zipWith (\ (ci,_) ei' -> (ci,ei')) cs es'))   
  -- eqs <- forM cs $ \ (ci,ei) -> do
  --           (tins,tout) <- freshForSymbol e ci
  --           mgu <- unifyM e (typeOf g') tout
  --           return (ei, mgu `o` foldr (:->) (TyVar n) tins)
  -- (s,es') <- sg `o` ctx ||- eqs
  -- return (s `o` sg
  --        , Cond (l, s n) (s `o` g') (zipWith (\ (ci,_) ei' -> (ci,ei')) cs es'))

ctx |- Fix l i es = do 
  fs <- const (TyVar <$> fresh) `mapM` es
  let tis = [foldr (:->) fi fs  | fi <- fs ]
  (s,es') <- ctx ||- zip es tis
  return (s,Fix (l, s `o` (fs!!i)) i es')
      
(||-) :: TContext -> [(Exp l,Type)] -> InferM (TypingError (Exp l)) (TSubst,[TypedExp l])      
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
       
infer :: Program l -> Either (TypingError (Exp l)) (TypedProgram l)
infer p = do 
  (_,te) <- run (signature p) ([] |- expression p)
  return p { expression = te }
