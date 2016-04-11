module Hoca.Data.MLTypes (
  -- * Types and Schemas
  TypeVariable 
  , TypeName
  , MLType (..)
  , SchemaVar (..)
  , isTArrow
  , isTVar
  , isTCon
  -- * Plain Types
  , Type
  , unify  
  -- * Type Schemas
  , TypeSchema
  , tsMatrix
  , curryType
  , uncurryType
  , uncurryUpto
  , bvar
  , fvar
  -- * Substitution
  , Substitution
  , idSubst
  , singletonSubst
  -- * Declarations and Signatures
  , Signature
  , TypeDecl (..)
  , TypeDeclaration (..)  
  , signatureToList
  , signatureFromList
  , mapSignature
  , decl
  -- * Classes
  , TypeTerm (..)
  , substitute
  , Substitutable (..)
  -- * Misc
  , variableNames
) where

import Data.Foldable (toList)
import           Control.Monad.Except
import           Data.List (nub)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Hoca.Utils (ppSeq)
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Control.Arrow (first)

---------------------------------------------------------------------- 
-- General
---------------------------------------------------------------------- 

type TypeVariable = Int
type TypeName = String

data MLType v = 
  TyVar v
  | TyCon TypeName [MLType v]
  | MLType v :-> MLType v
  deriving (Eq, Ord, Show, Functor, Foldable)  

substitute :: (v -> MLType v') -> MLType v -> MLType v'
substitute s (TyVar n) = s n
substitute s (TyCon n ts) = TyCon n (substitute s `map` ts)
substitute s (t1 :-> t2) = substitute s t1 :-> substitute s t2

class TypeTerm a where
  freeTV :: a -> [TypeVariable]
  boundTV :: a -> [TypeVariable]
  tvs :: a -> [TypeVariable]
  tvs a = freeTV a ++ boundTV a

isTVar :: MLType v -> Bool
isTVar (TyVar _) = True
isTVar _ = False

isTArrow :: MLType v -> Bool
isTArrow (_ :-> _) = True
isTArrow _ = False

isTCon :: MLType v -> Bool
isTCon (TyCon {}) = True
isTCon _ = False


---------------------------------------------------------------------- 
-- Plain types, i.e., all variables occur free
---------------------------------------------------------------------- 

type Type = MLType TypeVariable

instance TypeTerm Type where
  freeTV = toList
  boundTV _ = []


---------------------------------------------------------------------- 
-- Type schemas, i.e., types with bound variables
---------------------------------------------------------------------- 

data SchemaVar = BVar TypeVariable | FVar TypeVariable
  deriving (Eq, Ord)

bvar :: TypeVariable -> TypeSchema
bvar = TyVar . BVar

fvar :: TypeVariable -> TypeSchema
fvar = TyVar . FVar
  
type TypeSchema = MLType SchemaVar

instance TypeTerm TypeSchema where
  freeTV ts = [m | FVar m <- toList ts]
  boundTV ts = [m | BVar m <- toList ts]

tsMatrix :: TypeSchema -> Type
tsMatrix = fmap f where
  f (BVar i) = i
  f (FVar i) = i

curryType :: [Type] -> Type -> Type
curryType = flip (foldr (:->))

uncurryType :: Type -> ([Type], Type)
uncurryType (p :-> n) = first ((:) p) (uncurryType n)
uncurryType t = ([],t)

uncurryUpto :: Type -> Int -> Maybe ([Type], Type)
uncurryUpto tpe i | i <= 0 = Just ([],tpe)
uncurryUpto (n :-> t) i = do 
  (as,t') <- t `uncurryUpto` (i - 1)
  return (n:as,t')
uncurryUpto _ _ = Nothing  

---------------------------------------------------------------------- 
-- Type Declarations and signatures
---------------------------------------------------------------------- 

data TypeDecl = [Type] :~> Type
infixl 8 :~>

data TypeDeclaration f = f ::: TypeDecl
infixl 7 :::
           
type Signature f = Map f TypeDecl

signatureToList :: Signature f -> [TypeDeclaration f]
signatureToList = map (uncurry (:::)) . Map.toList

signatureFromList :: Ord f => [TypeDeclaration f] -> Signature f
signatureFromList = foldl (\ sig (f ::: td) -> Map.insert f td sig) Map.empty

mapSignature :: (TypeDeclaration f -> TypeDecl) -> Signature f -> Signature f
mapSignature fun = Map.mapWithKey (\ f td -> fun (f ::: td))

decl :: Ord f => f -> Signature f -> Maybe TypeDecl
decl = Map.lookup

---------------------------------------------------------------------- 
-- Type substitutions
---------------------------------------------------------------------- 

type Substitution = TypeVariable -> Type

idSubst :: Substitution 
idSubst = TyVar 

singletonSubst :: TypeVariable -> Type -> Substitution
singletonSubst v t v' = if v' == v then t else TyVar v'

class Substitutable a where
  o :: Substitution -> a -> a

instance Substitutable Type where  
  o = substitute

instance Substitutable TypeSchema where  
  s `o` (TyVar (FVar m)) = fromType (s m) where
    fromType = fmap FVar 
  _ `o` (TyVar (BVar m)) = TyVar (BVar m)
  s `o` (TyCon n ts) = TyCon n (map (o s) ts)
  s `o` (t1 :-> t2) = (s `o` t1) :-> (s `o` t2)
  
instance Substitutable Substitution where
  s1 `o` s2 = o s1 . s2


---------------------------------------------------------------------- 
-- Type unification
---------------------------------------------------------------------- 

unify :: [(Type,Type)] -> Either (Type,Type) Substitution
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
-- prettyprinting
----------------------------------------------------------------------

variableNames :: [String]
variableNames = [ [c] | c <- ['a'..'z']] ++ [ 'a' : show i | i <- [(1 :: Int)..] ]

prettyTyCon :: (PP.Pretty t, PP.Pretty v) => t -> [v] -> PP.Doc
prettyTyCon n [] = PP.pretty n
prettyTyCon n [t] = PP.pretty t PP.<+> PP.pretty n
prettyTyCon n ts = PP.parens (ppSeq PP.comma [PP.pretty t | t <- ts]) PP.<+> PP.pretty n

prettyTyVar :: TypeVariable -> PP.Doc
prettyTyVar v = PP.text ("'" ++ variableNames !! v)

instance PP.Pretty TypeSchema where
  pretty t = ppBVars btvs PP.<> PP.text "." PP.<+> PP.pretty (tsMatrix t) where
    btvs = nub [ m | BVar m <- toList t]
    ppBVars [] = PP.empty
    ppBVars bvs = PP.text "forall" PP.<+> ppSeq PP.space [ prettyTyVar v | v <- bvs ]

instance PP.Pretty Type where 
  pretty t = ppType t id where
    ppType (TyVar i) _ = prettyTyVar i
    ppType (TyCon n ts) _ = prettyTyCon n ts
    ppType (uncurryType -> (ts,tr)) p = p (PP.encloseSep PP.empty PP.empty (PP.text " -> ") [ppType ti PP.parens | ti <- ts ++ [tr]])


instance PP.Pretty f => PP.Pretty (Signature f) where 
    pretty ts = 
        PP.vcat [ PP.hang 2 (PP.fillBreak n (PP.pretty ci) PP.<+> PP.text "::" PP.<+> PP.pretty (declToType d))
                | ci ::: d <- l ] where
        l = signatureToList ts
        n = maximum  (0 : [ length (show (PP.pretty ci)) | ci ::: _ <- l])
        declToType (tins :~> tout) = foldr (:->) tout tins
