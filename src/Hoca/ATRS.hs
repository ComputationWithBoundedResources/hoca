-- | 

module Hoca.ATRS
       (
         -- * Types and Constructors
         ASym (..)
       , AView (..)
       , Term
       , Rule
       , atermM
       , aterm
       , app
       , fun
       , args
       , function
       , var
         -- * operations on terms
       , headSymbol
       , headVars
       , funsDL
       , funs
         -- * Typing
       , Type (..)
       , TypeDecl (..)
       , Signature
       , Env
       , inferTypes
         -- ** Typed Terms and Rules
       , TypedTerm
       , TypedRule
       , withType
       , unType
       , unTypeRule
       , unTypeRules
       , getType
       )
where

import qualified Data.Rewriting.Term as T
import qualified Data.Rewriting.Rule as R
import qualified Data.Rewriting.Rules as RS
import qualified Data.Rewriting.Substitution as S
import qualified Data.Rewriting.Substitution.Type as ST
import           Data.Rewriting.Substitution.Unify (unify)

import Data.Maybe (fromJust, isNothing)
import qualified Data.Map as Map
import           Control.Monad.RWS
import Control.Applicative (Applicative,(<$>),(<*>))
import Data.List (nub)
import Control.Arrow (first)
import Control.Monad.Error (MonadError, throwError)
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import qualified Control.Monad.State as State

data ASym f = Sym f | App deriving (Ord, Eq, Show)

type Term f v = T.Term (ASym f) v
type Rule f v = R.Rule (ASym f) v

data AView f v = Var v | Fun f [Term f v] | Term f v :@ Term f v

instance PP.Pretty f => PP.Pretty (ASym f) where
  pretty App = PP.text "@"
  pretty (Sym f) = PP.pretty f

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
fun f = T.Fun (Sym f)

var :: v -> Term f v
var = T.Var

headSymbol :: Term f v -> Maybe f
headSymbol (atermM -> Just (Fun f _)) = Just f
headSymbol (atermM -> Just (t1 :@ _)) = headSymbol t1
headSymbol _ = Nothing

headVars :: Term f v -> [v]
headVars (atermM -> Just (T.Var v :@ t2)) = v : headVars t2
headVars (T.Var _) = []
headVars (T.Fun _ ts) = concatMap headVars ts

funsDL :: Term f v -> [f] -> [f]
funsDL t l = [f | (Sym f) <- T.funsDL t (map Sym l)]

funs :: Term f v -> [f]
funs t = funsDL t []

function :: Term f v -> Maybe (Term f v)
function (atermM -> Just (t1 :@ _)) = function t1
function (atermM -> Just (Var v)) = Just (T.Var v)
function (atermM -> Just (Fun f ts)) = Just (T.Fun (Sym f) ts)
function _ = Nothing

args :: Term f v -> [Term f v]
args (atermM -> Just (t1 :@ t2)) = args t1 ++ [t2]
args _ = []

-- typing

data Type = Type :~> Type | BT Int deriving (Eq, Ord, Show)

type TypedTerm f v = T.Term (ASym f,Type) (v,Type)

type TypedRule f v = R.Rule (ASym f,Type) (v,Type)

data TypeDecl = TypeDecl { inputTypes :: [Type], outputType :: Type }
              deriving (Eq, Ord, Show)
                      
type Signature f = Map.Map f TypeDecl
type Env v = Map.Map v Type

instance PP.Pretty Type where
  pretty = pp False
    where
      pp _ (BT bt) = PP.text ( names !! bt)
        where names = (:[]) `map` ['A'..'Z'] ++ [show i | i <- [(1::Int)..]]
      pp paren (ta :~> tb) = encl (pp True ta PP.<+> PP.text "->" PP.<+> pp False tb)
        where encl d | paren = PP.lparen PP.<+> d PP.<+> PP.rparen
                     | otherwise = d
  
instance PP.Pretty TypeDecl where
  pretty td
    | null (inputTypes td) = PP.pretty (outputType td)
    | otherwise = PP.encloseSep PP.lbracket PP.rbracket PP.comma (map PP.pretty (inputTypes td))
                  PP.<+> PP.text "->" PP.<+> PP.pretty (outputType td)

instance (PP.Pretty f) => PP.Pretty (Signature f) where
  pretty sig = PP.vcat [ PP.pretty f PP.<+> PP.text "::" PP.<+> PP.pretty td | (f,td) <- Map.toList sig]

data TSym = TApp | TBase Int deriving (Eq, Ord, Show)

data TVar f = TFresh Int | TIn f Int | TOut f deriving (Eq, Ord, Show)
type TExp f = T.Term TSym (TVar f)

type UP f = [(TExp f, TExp f)]

newtype TInferM f a = 
  TInferM { runTInfer :: RWST () (UP f) Int (Either String) a }
  deriving (Applicative, Functor, Monad, MonadWriter (UP f), MonadState Int, MonadError String)

evalTInferM :: TInferM f a -> Either String (a, UP f)
evalTInferM m = evalRWST (runTInfer m) () 0

typeOf :: (Ord v, Ord f) => Env v -> Signature f -> Term f v -> Maybe Type
typeOf env sig t =
  case atermM t of
   Just (Var v) -> Map.lookup v env
   Just (Fun f _) -> outputType <$> Map.lookup f sig
   Just (t1 :@ t2) -> do
     tp1 <- typeOf env sig t1
     tp2 <- typeOf env sig t2     
     case tp1 of
      tp11 :~> tp22
        | tp11 == tp2 -> Just tp22
      _ -> Nothing
   _ -> Nothing       

getType :: TypedTerm f v -> Type
getType (T.Var (_,tp)) = tp
getType (T.Fun (_,tp) _) = tp

withType :: (Ord v, Ord f) => Env v -> Signature f -> Term f v -> Maybe (TypedTerm f v)
withType env sig t@(T.Var v) = do
  tp <- typeOf env sig t
  return (T.Var (v,tp))
withType env sig t@(T.Fun f ts) = do
  tp <- typeOf env sig t
  ts' <- mapM (withType env sig) ts
  return (T.Fun (f,tp) ts')

unType :: TypedTerm f v -> Term f v
unType = T.map fst fst

mapRule :: (R.Term f1 v1 -> R.Term f v) -> R.Rule f1 v1 -> R.Rule f v
mapRule f r = R.Rule{ R.lhs = f (R.lhs r), R.rhs = f (R.rhs r) }

unTypeRule :: TypedRule f v -> Rule f v
unTypeRule  = mapRule unType

unTypeRules :: [TypedRule f v] -> [Rule f v]
unTypeRules = map unTypeRule

inferTypes :: (Ord v, Ord f, Eq v) => [(Int, Rule f v)] -> Either String (Signature f, [(Int, (TypedRule f v,Env v))])
inferTypes rs = do
  (es,up) <- evalTInferM (mapM typeRuleM rs)
  assign <- ST.toMap <$> solveUP up
  return $ flip State.evalState (Map.empty, 0::Int) $ do
        sig <- mkSignature assign
        envs <- mapM (mkEnv assign) es
        return (sig, [ (i,(mapRule (fromJust . withType env sig) rl, env)) | ((i,rl),env) <- zip rs envs ])
  where
    freshM = modify succ >> (TFresh <$> get)
    freshVar = T.Var <$> freshM
    
    a =~ b = tell [(a,b)]

    inTypeVar f i = T.Var (TIn f i)
    outTypeVar f = T.Var (TOut f)
    
    e |- (aterm -> Var v, a) = T.Var (fromJust (Map.lookup v e)) =~ a
    e |- (aterm -> t1 :@ t2, a) = do
      b <- freshVar
      e |- (t1, T.Fun TApp [b,a])
      e |- (t2, b)
    e |- (aterm -> Fun f ts, a) = do
      outTypeVar f =~ a
      mapM_ (\(i,ti) -> e |- (ti, inTypeVar f i)) (zip [0..] ts)
    _ |- _ = throwError "non-applicative term trs given"  

    typeRuleM (_,R.Rule lhs rhs) = do
      let vs = nub (T.vars lhs)
      e <- foldM (\e v -> Map.insert v <$> freshM <*> return e) Map.empty vs
      tl <- freshVar
      tr <- freshVar
      e |- (lhs, tl)
      e |- (rhs, tr)
      tl =~ tr
      return e

    solveUP [] = return (ST.fromMap Map.empty)
    solveUP ((c1,c2):cs) = do
      u <- solveUP cs
      u1 <- maybe (throwError "non-unifiable") return (unify (S.apply u c1) (S.apply u c2))
      return (S.compose u1 u)

    toTypeM assign (T.Var v) = do
      (env, fresh) <- State.get
      case Map.lookup v env of
       Nothing ->
         case Map.lookup v assign of
          mt | isNothing mt || mt == Just (T.Var v) -> do
                 State.put (Map.insert v (BT fresh) env, fresh+1)
                 return (BT fresh)
          mt -> do
            tp <- toTypeM assign (fromJust mt)
            State.modify (first (Map.insert v tp))
            return tp
       Just tp -> return tp
    toTypeM _ (T.Fun (TBase bt) _) = return (BT bt)
    toTypeM assign (T.Fun TApp [t1,t2]) = do
      tp1 <- toTypeM assign t1
      tp2 <- toTypeM assign t2
      return (tp1 :~> tp2)
    toTypeM _ _ = error "toTypeM: TApp supplied with wrong number of arguments"

    mkEnv assign e =
      Map.fromList <$>
      mapM (\ (v,t) -> do { tp <- toTypeM assign (T.Var t); return (v,tp) })
      (Map.toList e)
      
    mkSignature assign =
      foldM (\ sig (f,ar) -> do
                ins <- mapM (toTypeM assign . inTypeVar f) [0..ar-1]
                out <- toTypeM assign (outTypeVar f)
                return (Map.insert f (TypeDecl ins out) sig))       
      Map.empty fs
      where 
        fs = nub [ (f,ar) | (Sym f,ar) <- RS.funs (map (mapRule T.withArity . snd) rs)]

