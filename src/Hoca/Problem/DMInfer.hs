{-# LANGUAGE FunctionalDependencies #-}

module Hoca.Problem.DMInfer (
  TTerm (..)
  , typeOf
  , Inferrable (..)
  , check
  , infer
  , inferWith
  , TypingError (..)
) where

import Control.Monad.Except
import Control.Arrow (second)
import Hoca.Problem.Type
import Hoca.Data.MLTypes
import Data.Rewriting.Applicative.Term
import Data.Rewriting.Applicative.Rule
import qualified Data.Map as Map
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Control.Monad.RWS

data TTerm f v =
  TpVar Type v
  | TpFun Type f [TTerm f v]
  | TpApp Type (TTerm f v) (TTerm f v)

typeOf :: TTerm f v -> Type
typeOf (TpVar tp _) = tp
typeOf (TpFun tp _ _) = tp
typeOf (TpApp tp _ _) = tp

instance Substitutable (TTerm f v) where
  s `o` TpVar tpe v = TpVar (s `o` tpe) v
  s `o` TpFun tpe f ts = TpFun (s `o` tpe) f (map (s `o`) ts)
  s `o` TpApp tpe t1 t2 = TpApp (s `o` tpe) (s `o` t1) (s `o` t2)


data TypingError f v = 
  NonUnifiable Type Type (ATerm f v)
  | InvalidNumArguments Int Int f
  | NonApplicativeTerm (ATerm f v)
  | DeclarationMissing f

instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (TypingError f v) where
    pretty err = 
        PP.text "Cannot type term, exception was:"
        PP.<$$> pp err 
        where
          pp (NonUnifiable t1 t2 e) = 
              PP.text "Could not match expected type" 
              PP.<+> PP.squotes (PP.pretty t2)
              PP.<+> PP.text "with actual type"
              PP.<+> PP.squotes (PP.pretty t1)
              PP.<> PP.text "."
              PP.<$$> PP.text "In the term" PP.<+> PP.squotes (PP.pretty e)
          pp (InvalidNumArguments i j f) = 
              PP.text "The symbol" PP.<+> PP.squotes (PP.pretty f) 
              PP.<+> PP.text "expects" PP.<+> PP.int i PP.<+> PP.text "arguments, but"
              PP.<+> PP.int j PP.<+> PP.text "were given."        
          pp (NonApplicativeTerm _) = 
              PP.text "Non-applicative term given."
          pp (DeclarationMissing f) = 
              PP.text "Declaration for symbol" PP.<+> PP.squotes (PP.pretty f) PP.<+> PP.text "misssing."

data InferState f v = InferState {
  varEnv :: TypingEnv v
  , declEnv :: Signature f
  , unused :: !Int
}

instance Substitutable (Signature f) where
    s `o` sig = Map.map (\ (tins :~> tout) -> map (s `o`) tins :~> s `o` tout) sig

instance Substitutable (InferState f v) where
  s `o` st = st { varEnv = s `o` varEnv st, declEnv = s `o` declEnv st }


newtype InferM f v a = InferM { execIM_ :: RWST (Signature f) () (InferState f v) (Except (TypingError f v)) a } deriving
    ( Applicative, Functor, Monad
    , MonadReader (Signature f)
    , MonadState (InferState f v)
    , MonadError (TypingError f v) )

execInferM :: Signature f -> [(v, Type)] -> InferM f v a -> Either (TypingError f v) (a, Signature f)
execInferM sig env m = runExcept (fst <$> evalRWST (execIM_ m') sig (InferState env Map.empty f)) where
  f = 1 + maximum (0 : concatMap (freeTV . snd) env)
  m' = (,) <$> m <*> (declEnv <$> get)
    

uniques :: Int -> InferM f v [TypeVariable]
uniques n = do {st <- get; put st{ unused = unused st + n} ; return [unused st .. unused st + n - 1] }

unique :: InferM f v TypeVariable
unique = head <$> uniques 1

unifyM :: Type -> Type -> ATerm f v -> InferM f v Substitution
unifyM tp1 tp2 t = 
  case unify [(tp1,tp2)] of 
   Left (t1,t2) -> throwError (NonUnifiable t1 t2 t)
   Right mgu -> return mgu

declarationOf :: Ord f => (f,Int) -> InferM f v TypeDecl
declarationOf (f,ar) = do
  m1 <- decl f <$> ask
  m2 <- decl f <$> declEnv <$> get
  maybe create instantiate (m1 `mplus` m2)
  where
    instantiate (ins :~> out)
      | length ins /= ar =
          throwError (InvalidNumArguments (length ins) ar f)
      | otherwise = do
          s <- mkSubst <$> uniques n
          return (map (s `o`) ins :~> s `o` out)
      where 
        n = 1 + maximum (0:concatMap freeTV (out:ins))
        mkSubst vs = \ v -> TyVar (vs!!v) 
      
    create = do
      td <- (:~>) <$> (map TyVar <$> uniques ar) <*> (TyVar <$> unique)
      modify ( \ st -> st { declEnv = Map.insert f td (declEnv st) } )
      return td

checkM :: (Ord f, Eq v) => ATerm f v -> Type -> InferM f v (Substitution, TTerm f v)
checkM (Var v) tp = do
  st <- get
  case lookup v (varEnv st) of
    Nothing -> do
      put st{ varEnv = (v,tp) : varEnv st}
      return (idSubst, TpVar tp v)
    Just tp' -> do 
      mgu <- unifyM tp tp' (Var v)
      modify (mgu `o`)
      return (mgu, TpVar (mgu `o` tp) v)
checkM (atermM -> Just (TFun f ts)) tp = do
  (ins :~> out) <- declarationOf (f,length ts)
  mgu <- unifyM out tp (Fun (Sym f) ts)
  modify (mgu `o`)
  (s,ts') <- checkL idSubst [] (zip ts (map (mgu `o`) ins))
  return (s `o` mgu, TpFun (s `o` mgu `o` out) f ts')
    where 
      checkL s tts [] = return (s,tts)
      checkL s tts ((ti,tpi):tps) = do
        (si,ti') <- checkM ti tpi
        checkL (si `o` s) (map (si `o`) tts ++ [ti']) (map (second (si `o`)) tps)
checkM (atermM -> Just (t1 :@ t2)) tp = do
  v <- TyVar <$> unique
  (s1,t1') <- checkM t1 (v :-> tp)
  (s2,t2') <- checkM t2 (s1 `o` v)
  return (s2 `o` s1, TpApp (s2 `o` s1 `o` tp) t1' t2')
checkM t __ = throwError (NonApplicativeTerm t)

checkRuleM :: (Ord f, Eq v) => ARule f v -> Type -> InferM f v (TRule f v)
checkRuleM rl tp = do 
  oldEnv <- varEnv <$> get
  (s1, _) <- checkM (lhs rl) tp
  (s2, _) <- checkM (rhs rl) (s1 `o` tp)
  env <- varEnv <$> get
  modify (\ st -> st { varEnv = oldEnv } )
  return TRule { theRule = rl
               , theEnv = env
               , theType = s2 `o` s1 `o` tp}


class Inferrable c f v | c -> f, c -> v where
  type TypeAnnotated c
  typeCheckM :: (Eq v, Ord f) => c -> Type -> InferM f v (TypeAnnotated c)

instance Inferrable (ATerm f v) f v where
  type TypeAnnotated (ATerm f v) = TTerm f v
  typeCheckM c t = snd <$> checkM c t

instance Inferrable (ARule f v) f v where
  type TypeAnnotated (ARule f v) = TRule f v
  typeCheckM = checkRuleM 

withEmptyDeclEnvAsserted :: InferM f v a -> InferM f v a
withEmptyDeclEnvAsserted m = do
  a <- m
  e <- declEnv <$> get
  case Map.toList e of
    [] -> return a
    ((f,_):_) -> throwError (DeclarationMissing f)

check :: (Inferrable c f v, Eq v, Ord f) => Signature f -> TypingEnv v -> c -> Type -> Either (TypingError f v) (TypeAnnotated c)
check sig tenv c tpe = fst <$> execInferM sig tenv (withEmptyDeclEnvAsserted (typeCheckM c tpe))

inferWith :: (Inferrable c f v, Eq v, Ord f) => Signature f -> TypingEnv v -> c -> Either (TypingError f v) (TypeAnnotated c)
inferWith sig tenv c = fst <$> execInferM sig tenv (withEmptyDeclEnvAsserted ((TyVar <$> unique) >>= typeCheckM c))

infer :: (Eq v, Ord f) => [ARule f v] -> Either (TypingError f v) ([TRule f v], Signature f)
infer rs = execInferM Map.empty [] (forM rs $ \ r -> (TyVar <$> unique) >>= checkRuleM r)
