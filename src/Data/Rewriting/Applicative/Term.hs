-- | Applicative Term Rewrite Systems, modeled as term rewrite systems over a signature
-- of type @'ASym' f@. 

module Data.Rewriting.Applicative.Term
       (
         -- * Types and Constructors
         ASym (..)
       , AView (..)
       , ATerm
       , atermM
       , aterm
       , app
       , fun
       , var
         -- * Operations on Terms
       , wellformed
       , aform
       , hd         
       , args

       , headSymbol
       , headVars
       , funsDL
       , funs
         -- * Re-exported Term operatons
       , module Data.Rewriting.Term
       )
where

import qualified Data.Rewriting.Term as T

import           Data.Rewriting.Term hiding (map, funs, funsDL, Term(..))

import Data.Maybe (fromJust)
import Control.Applicative ((<$>))
import qualified Text.PrettyPrint.ANSI.Leijen as PP

--------------------------------------------------------------------------------
-- applicative terms
--------------------------------------------------------------------------------


data ASym f = Sym f -- ^ n-ary function symbol
            | App   -- ^ binary application symbol
            deriving (Ord, Eq, Show)

type ATerm f v = T.Term (ASym f) v


-- constructors

-- | a term is well-formed if all occurrences of the application symbol 'App' are binary
--
-- >>> wellformed (T.Fun App [T.Var 'x', T.Var 'y'])
-- True
--
-- >>> wellformed (T.Fun App [T.Var 'x'])
-- False
wellformed :: ATerm f v -> Bool
wellformed = T.fold (const True) wf where
  wf App wfs@[_,_] = and wfs
  wf (Sym _) wfs = and wfs
  wf _ _ = False

-- | constructor for application
app :: ATerm f v -> ATerm f v -> ATerm f v
app t1 t2 = T.Fun App [t1,t2]

-- | constructor for n-ary function symbols
fun :: f -> [ATerm f v] -> ATerm f v
fun f = T.Fun (Sym f)

-- | constructor for variables
var :: v -> ATerm f v
var = T.Var

instance PP.Pretty f => PP.Pretty (ASym f) where
  pretty App = PP.text "@"
  pretty (Sym f) = PP.pretty f


-- applicative view of term

-- | View for applicative terms
data AView f v = Var v -- ^ Variable
               | Fun f [ATerm f v] -- ^ n-ary function application 
               | ATerm f v :@ ATerm f v -- ^ application


-- | constructs applicative view of a term, returns 'Nothing' iff the given term is not 'wellformed'
atermM :: ATerm f v -> Maybe (AView f v)
atermM (T.Var v) = Just (Var v)
atermM (T.Fun App [t1,t2]) = Just (t1 :@ t2)
atermM (T.Fun (Sym f) ts) = Just (Fun f ts)
atermM _ = Nothing

-- | partial version of 'atermM', total on 'wellformed' terms
aterm :: ATerm f v -> AView f v
aterm = fromJust . atermM

-- | translates an applicative term @s t1 ... tn@ into
-- the pair @(s,[t1 ... tn])@ provided the given term is 'wellformed'.
-- The functions 'hd' and 'args' return @s@ and the list @[t1 ... tn]@, respectively.
--
-- prop> wellformed t ==> isJust (aform t)
--
-- prop> aform t == Just (s,ts)  ==>  hd t == Just s && args t == ts
aform :: ATerm f v -> Maybe (ATerm f v, [ATerm f v])
aform (atermM -> Nothing) = Nothing
aform (atermM -> Just (t1 :@ t2)) = do
  (c,as) <- aform t1
  return (c, as ++ [t2])
aform t = return (t,[])

-- | Returns the head of an applicative term, see 'aform'
hd :: ATerm f v -> Maybe (ATerm f v)
hd t = fst <$> aform t

-- | Returns the arguments of an applicative term, see 'aform'
args :: ATerm f v -> Maybe [ATerm f v]
args t = snd <$> aform t

-- | Returns the root symbol of the head term, if existing
--
-- prop> hd t == Just (T.Fun f ts)  <==>  headSymbol t == Just f
headSymbol :: ATerm f v -> Maybe f
headSymbol (atermM -> Just (Fun f _)) = Just f
headSymbol (atermM -> Just (t1 :@ _)) = headSymbol t1
headSymbol _ = Nothing

-- | Returns all variables in head position
--
-- >>> headVars (T.Var 'x')
-- []
--
-- >>> headVars (T.Fun App [Var 'x', T.Var 'y'])
-- ['x']
--
-- >>> headVars (T.Fun App [Var 'x', (T.Fun App [Var 'x', T.Var 'y'])])
-- ['x','x']
-- 
-- >>> headVars (T.Fun (Sym 'f') [T.Fun App [Var 'x', Var 'y']]
-- ['x']
headVars :: ATerm f v -> [v]
headVars (atermM -> Just (T.Var v :@ t2)) = v : headVars t2
headVars (T.Var _) = []
headVars (T.Fun _ ts) = concatMap headVars ts

-- | returns all function symbols occurring in the given term
funs :: ATerm f v -> [f]
funs t = funsDL t []

-- | difference list version of 'funs'
funsDL :: ATerm f v -> [f] -> [f]
funsDL t fs = [f | (Sym f) <- T.funsDL t [Sym f | f <- fs]]



