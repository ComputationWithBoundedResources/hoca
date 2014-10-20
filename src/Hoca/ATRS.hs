-- | 

module Hoca.ATRS where

import qualified Data.Rewriting.Term as T
import qualified Data.Rewriting.Rule as R
import qualified Data.Rewriting.Rules as RS
import qualified Data.Rewriting.Substitution as S
import qualified Data.Rewriting.Substitution.Type as ST
import           Data.Rewriting.Substitution.Unify (unify)

import Data.Maybe (fromJust)
import qualified Data.Map as Map
import           Control.Monad.RWS
import Control.Applicative (Applicative,(<$>),(<*>))
import Data.List (nub)
import Control.Monad.Error (MonadError, throwError)
import qualified Text.PrettyPrint.ANSI.Leijen as PP

data ASym f = Sym f | App deriving (Ord, Eq, Show)

type Term f v = T.Term (ASym f) v
type Rule f v = R.Rule (ASym f) v

data AView f v = Var v | Fun f [Term f v] | Term f v :@ Term f v

atermM :: Term f v -> Maybe (AView f v)
atermM (T.Var v) = Just (Var v)
atermM (T.Fun App [t1,t2]) = Just (t1 :@ t2)
atermM (T.Fun (Sym f) ts) = Just (Fun f ts)
atermM _ = Nothing

aterm :: Term f v -> AView f v
aterm = fromJust . atermM


app :: Term f v -> Term f v -> Term f v
app t1 t2 = T.Fun App [t1,t2]

fun :: f -> [Term f v] -> Term f v
fun f ts = T.Fun (Sym f) ts

var :: v -> Term f v
var = T.Var

headSymbol :: Term f v -> Maybe f
headSymbol (atermM -> Just (Fun f _)) = Just f
headSymbol (atermM -> Just (t1 :@ _)) = headSymbol t1
headSymbol _ = Nothing

funsDL :: Term f v -> [f] -> [f]
funsDL t l = [f | (Sym f) <- T.funsDL t (map Sym l)]

-- typing


data Type bt = Type bt :~> Type bt | BT bt
data TypeDecl bt = TypeDecl { inputTypes :: [Type bt], outputType :: Type bt }

type Signature f bt = Map.Map f (TypeDecl bt)

instance PP.Pretty bt => PP.Pretty (Type bt) where
  pretty (BT bt) = PP.pretty bt
  pretty (ta :~> tb) = PP.pretty ta PP.<+> PP.text "->" PP.<+> PP.pretty tb
  
instance PP.Pretty bt => PP.Pretty (TypeDecl bt) where
  pretty td = PP.encloseSep PP.lbracket PP.rbracket PP.comma (map PP.pretty (inputTypes td))
              PP.<+> PP.text "->" PP.<+> PP.pretty (outputType td)

instance (PP.Pretty f, PP.Pretty bt) => PP.Pretty (Signature f bt) where
  pretty sig = PP.vcat [ PP.pretty f PP.<+> PP.text "::" PP.<+> PP.pretty td | (f,td) <- Map.toList sig]

data TSym bt = TApp
             | TBase bt
          deriving (Eq, Ord, Show)

data TVar f = TFresh Int
            | TIn f Int
            | TOut f
            deriving (Eq, Ord, Show)
type TExp f bt = T.Term (TSym bt) (TVar f)

type UP f bt = [(TExp f bt, TExp f bt)]

newtype TInferM f bt a = 
  TInferM { runTInfer :: RWST () (UP f bt) Int (Either String) a }
  deriving (Applicative, Functor, Monad, MonadWriter (UP f bt), MonadState Int, MonadError String)

signature :: (Eq bt, Ord v, Ord f) => bt -> [Rule f v] -> Either String (Signature f bt)
signature deftpe rs = toSignature <$> signature' rs
  where
    toSignature tassign =
      Map.fromList [(f,TypeDecl ins out)
                   | (f,ar) <- fs
                   , let ins = map (argType f) [0..ar-1]
                         out = retType f ]
      where
        fs = nub [ (f,ar) | (Sym f,ar) <- RS.funs (map (R.map T.withArity) rs)] 
        argType f i = fromAssign (T.Var (TIn f i))
        retType f = fromAssign (T.Var (TOut f))
        fromAssign (T.Var v) =
          case Map.lookup v (ST.toMap tassign) of
           Nothing -> BT deftpe
           Just (T.Var v') | v == v' -> BT deftpe
           Just t -> fromAssign t
        fromAssign (T.Fun (TBase bt) _) = BT bt
        fromAssign (T.Fun TApp [t1,t2]) = fromAssign t1 :~> fromAssign t2
        fromAssign _ = error "fromAssign: TApp with wrong arity"

signature' :: (Eq bt, Ord v, Ord f) => [Rule f v] -> Either String (ST.GSubst (TVar f) (TSym bt) (TVar f))
signature' rs = evalTInferM (mapM typeM rs) >>= solveConstraints
  where
    evalTInferM m = snd <$> evalRWST (runTInfer m) () 0
    freshVar = modify succ >> (T.Var <$> TFresh <$> get)
    
    initialEnv t =
      foldM (\e v -> Map.insert v <$> freshVar <*> return e)
      Map.empty (nub (T.vars t))

    lookupEnv e v = fromJust (Map.lookup v e)
    
    a =~ b = tell [(a,b)]
    
    a ~> b = T.Fun TApp [a,b]
    
    typeM (R.Rule lhs rhs) = do
      e <- initialEnv lhs
      tl <- freshVar
      tr <- freshVar
      e |- (lhs, tl)
      e |- (rhs, tr)
      tl =~ tr

    e |- (aterm -> Var v, a) = lookupEnv e v =~ a
    e |- (aterm -> t1 :@ t2, a) = do
      b <- freshVar
      e |- (t1, b ~> a)
      e |- (t2, b)
    e |- (aterm -> Fun f ts, a) = do
      T.Var (TOut f) =~ a
      mapM_ (\(i,ti) -> e |- (ti, T.Var (TIn f i))) (zip [0..] ts)
    _ |- _ = throwError "non-applicative term trs given"  

    solveConstraints [] = return (ST.fromMap Map.empty)
    solveConstraints ((c1,c2):cs) = do
      u <- solveConstraints cs
      u1 <- maybe (throwError "non-unifiable") return (unify (S.apply u c1) (S.apply u c2))
      return (S.compose u1 u)

          
