module Hoca.Problem.DMInfer (
  inferWith
  , inferWithR
  , inferWithT
) where

import Control.Monad (when)
import Control.Monad.Except (throwError)
import Control.Arrow (second)
import Hoca.Problem.Type
import Hoca.Data.MLTypes
import Data.Rewriting.Applicative.Term
import Data.Rewriting.Applicative.Rule

data TypingError f v = 
  NonUnifiable Type Type
  | DeclarationMissing f 
  | InvalidNumArguments Int Int f
  | NonApplicativeTerm (ATerm f v)

type TInferM f v a = InferM f (TypingError f v) a

unifyM :: Type -> Type -> TInferM f v Substitution
unifyM tp1 tp2 = 
  case unify [(tp1,tp2)] of 
   Left (t1,t2) -> throwError (NonUnifiable t1 t2)
   Right mgu -> return mgu

(|-) :: (Ord f, Eq v) => TypingEnv v -> (ATerm f v, Type) -> TInferM f v (Substitution,TypingEnv v)
env |- (Var v, tp) = 
  case lookup v env of 
   Nothing -> return (idSubst,(v,tp):env)
   Just tp' -> do 
     s <- unifyM tp tp'
     return (s, s `o` env)
env |- (atermM -> Just (TFun f ts), tp) = do
  mtd <- freshInstanceFor f
  case mtd of 
   Nothing -> throwError (DeclarationMissing f)
   Just (_ ::: fins :~> fout) -> do 
     when (length fins /= length ts) $ 
       throwError (InvalidNumArguments (length fins) (length ts) f)
     mgu <- unifyM fout tp
     (mgu `o` env) ||- (zip ts (map (mgu `o`) fins), mgu)
env |- (atermM -> Just (t1 :@ t2), tp) = do
  v <- TyVar <$> freshVar
  (s1,env1) <- env |- (t1, v :-> tp)
  (s2,env2) <- env1 |- (t2, s1 `o` v)
  return (s2 `o` s1, env2)
_   |- (t,_) = throwError (NonApplicativeTerm t)

(||-) :: (Ord f, Eq v) => TypingEnv v -> ([(ATerm f v, Type)], Substitution) -> TInferM f v (Substitution,TypingEnv v)
env ||- ([],s) = return (s,env)
env ||- ((t,tp) : ts,s) = do 
  (s',env') <- env |- (t,tp)
  env' ||- (map (second (s' `o`)) ts,s' `o` s)

inferRuleM :: (Ord f, Eq v) => ARule f v -> TInferM f v (TRule f v)
inferRuleM rl = do 
  v <- freshVar
  (s,env)  <- []  |- (lhs rl,TyVar v)
  (s',env') <- env |- (rhs rl,s v)
  return TRule { theRule = rl
               , theEnv = env'
               , theType = (s' `o` s) v}

inferWithR :: (Ord f, Eq v) => Signature f -> ARule f v -> Either (TypingError f v) (TRule f v)
inferWithR sig = runInferM sig . inferRuleM

inferWithT :: (Ord f, Eq v) => Signature f -> ATerm f v -> Either (TypingError f v) (Type,TypingEnv v)
inferWithT sig t = runInferM sig $ do 
  v <- freshVar
  (s,env) <- [] |- (t,TyVar v)
  return (s v,env)


inferWith :: (Ord f, Eq v) => Signature f -> [ARule f v] -> Either (TypingError f v) [TRule f v]
inferWith sig = runInferM sig . mapM inferRuleM

