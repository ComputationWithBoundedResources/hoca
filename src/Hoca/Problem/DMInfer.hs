module Hoca.Problem.DMInfer (
  inferWith
  , inferWithR
  , inferWithT
  , infer
  , TypingError (..)
) where

import Control.Monad (when, mplus, replicateM, foldM)
import Control.Monad.Except (throwError)
import Control.Arrow (second)
import Hoca.Problem.Type
import Hoca.Data.MLTypes
import Data.Rewriting.Applicative.Term
import Data.Rewriting.Applicative.Rule
import qualified Data.Rewriting.Applicative.Rules as RS
import qualified Data.Map as Map
import Data.List (nub)
import qualified Text.PrettyPrint.ANSI.Leijen as PP

data TypingError f v = 
  NonUnifiable Type Type (ATerm f v)
  | DeclarationMissing f 
  | InvalidNumArguments Int Int f
  | NonApplicativeTerm (ATerm f v)

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
          pp (DeclarationMissing f) = 
              PP.text "Cannot find function declaration of symbol" PP.<+> PP.squotes (PP.pretty f)
          pp (InvalidNumArguments i j f) = 
              PP.text "The symbol" PP.<+> PP.squotes (PP.pretty f) 
              PP.<+> PP.text "expects" PP.<+> PP.int i PP.<+> PP.text "arguments, but"
              PP.<+> PP.int j PP.<+> PP.text "were given."        
          pp (NonApplicativeTerm _) = 
              PP.text "Non-applicative term given."


type TInferM f v a = InferM f (TypingError f v) a

unifyM :: Type -> Type -> ATerm f v -> TInferM f v Substitution
unifyM tp1 tp2 t = 
  case unify [(tp1,tp2)] of 
   Left (t1,t2) -> throwError (NonUnifiable t1 t2 t)
   Right mgu -> return mgu

type DeclEnv f = Signature f

instance Substitutable (DeclEnv f) where
    s `o` denv = Map.map (\ (tins :~> tout) -> map (s `o`) tins :~> s `o` tout) denv

(|-) :: (Ord f, Eq v) => (TypingEnv v, DeclEnv f) -> (ATerm f v, Type) -> TInferM f v (Substitution,TypingEnv v, DeclEnv f)
(env,denv) |- (Var v, tp) = 
  case lookup v env of 
   Nothing -> return (idSubst,(v,tp):env, denv)
   Just tp' -> do 
     s <- unifyM tp tp' (Var v)
     return (s, s `o` env, s `o` denv)
(env,denv) |- (atermM -> Just (TFun f ts), tp) = do
  mtd <- freshInstanceFor f
  case mtd `mplus` ((:::) f <$> Map.lookup f denv) of 
    Nothing -> throwError (DeclarationMissing f)     
    Just (_ ::: fins :~> fout) -> do 
       when (length fins /= length ts) $ 
         throwError (InvalidNumArguments (length fins) (length ts) f)
       mgu <- unifyM fout tp (Fun (Sym f) ts)
       (mgu `o` env, mgu `o` denv) ||- (zip ts (map (mgu `o`) fins), mgu)
(env,denv) |- (atermM -> Just (t1 :@ t2), tp) = do
  v <- TyVar <$> freshVar
  (s1,env1, denv1) <- (env,denv) |- (t1, v :-> tp)
  (s2,env2, denv2) <- (env1,denv1) |- (t2, s1 `o` v)
  return (s2 `o` s1, env2,denv2)
_   |- (t,_) = throwError (NonApplicativeTerm t)

(||-) :: (Ord f, Eq v) => (TypingEnv v, DeclEnv f) -> ([(ATerm f v, Type)], Substitution) -> TInferM f v (Substitution,TypingEnv v, DeclEnv f)
(env,denv) ||- ([],s) = return (s,env,denv)
(env,denv) ||- ((t,tp) : ts,s) = do 
  (s',env',denv') <- (env,denv) |- (t,tp)
  (env',denv') ||- (map (second (s' `o`)) ts,s' `o` s)

inferRuleM :: (Ord f, Eq v) => DeclEnv f -> ARule f v -> TInferM f v (DeclEnv f, TRule f v)
inferRuleM declEnv rl = do 
  v <- freshVar
  (s,env,denv)  <- ([],declEnv)  |- (lhs rl,TyVar v)
  (s',env',denv') <- (env,denv) |- (rhs rl,s v)
  return (denv' 
         , TRule { theRule = rl
               , theEnv = env'
               , theType = (s' `o` s) v})

inferWithR :: (Ord f, Eq v) => Signature f -> ARule f v -> Either (TypingError f v) (TRule f v)
inferWithR sig = runInferM sig . fmap snd . inferRuleM Map.empty

inferWithT :: (Ord f, Eq v) => Signature f -> ATerm f v -> Either (TypingError f v) (Type,TypingEnv v)
inferWithT sig t = runInferM sig $ do 
  v <- freshVar
  (s,env,_) <- ([],Map.empty) |- (t,TyVar v)
  return (s v,env)


inferWith :: (Ord f, Eq v) => Signature f -> [ARule f v] -> Either (TypingError f v) [TRule f v]
inferWith sig = runInferM sig . mapM (fmap snd . inferRuleM Map.empty)

infer :: (Ord f, Eq v) => [ARule f v] -> Either (TypingError f v) (Signature f,[TRule f v])
infer rs = runInferM Map.empty $ do 
  denv <- initialDeclEnv (nub (RS.funs (mapRule withArity `map` rs)))
  foldM (\ (denv',trs) rl -> do 
              (denv'',trl) <- inferRuleM denv' rl
              return (denv'', trl:trs))
               (denv,[]) rs
      where 
        initialDeclEnv fs = Map.fromList <$> sequence [ initialDecl f n | (f,n) <- fs ]
        initialDecl f n = do
             (ot:its) <- replicateM (n+1) (TyVar <$> freshVar)
             return (f, its :~> ot)
