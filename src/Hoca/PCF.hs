-- | call by value PCF core with data types
module Hoca.PCF
  ( Exp (..)
  , Symbol (..)
--  , Label (..)

    -- * constructors
  , symbol
    -- * operations
  , constructors
    -- * reduction
  , beta
  , cond
  , fixCBV
  , nf
  , cbv
  ) where

import           Control.Applicative ((<$>), (<|>))
import qualified Data.Set as Set
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Control.Monad (foldM)

data Symbol = Symbol { sname :: String, sarity :: Int } deriving (Show, Eq, Ord)

symbol :: String -> Int -> Symbol
symbol = Symbol

type Variable = Int
data Exp l =
  Var Variable
  | Con Symbol [Exp l]
  | Bot
  | Abs (Maybe l) (Exp l)
  | App (Exp l) (Exp l)
  | Cond (Exp l) [(Symbol, (Exp l))]
  | Fix (Exp l)
  deriving (Show, Eq)

instance PP.Pretty Symbol where
  pretty = PP.bold . PP.text . sname

($$) :: PP.Doc -> PP.Doc -> PP.Doc
pa $$ pb = PP.align (pa PP.<$> PP.indent 1 pb)

(//) :: PP.Doc -> PP.Doc -> PP.Doc
pa // pb = PP.align (pa PP.</> pb)

instance PP.Pretty l => PP.Pretty (Exp l) where
  pretty (Var i) = PP.underline (PP.int i)
  pretty (Con f as) =
    PP.pretty f PP.<> PP.tupled [PP.pretty ai | ai <- as]
  pretty Bot = PP.bold (PP.text "_|_")
  pretty (Abs l e) =
    PP.parens (PP.bold (PP.text "λ") PP.<+> ppl l // PP.pretty e)
    where ppl = maybe (PP.empty) (\ v -> PP.pretty v PP.<> PP.text ".")
  pretty (App e1 e2) =
    PP.parens (PP.pretty e1 // PP.pretty e2)
  pretty (Fix e) =
    PP.parens (PP.bold (PP.text "fix") $$ PP.pretty e)
  pretty (Cond e cs) =
    PP.parens ((PP.bold (PP.text "caseC") PP.<+> PP.pretty e PP.<+> PP.bold (PP.text "of"))
               $$ PP.vsep [ PP.pretty g PP.<+> PP.text "->" PP.<+> PP.pretty e'
                          | (g,e') <- cs ])

constructors :: Exp l -> Set.Set Symbol
constructors (Con g _) = Set.singleton g
constructors (Abs _ e) = constructors e
constructors (App e1 e2) = constructors e2 `Set.union` constructors e1
constructors (Cond e cs) = foldl f (constructors e) cs
  where f fs (g,ei) = Set.insert g (constructors ei `Set.union` fs)
constructors (Fix e) = constructors e
constructors _ = Set.empty


-- * substitution 
shift :: Int -> Exp l -> Exp l
shift = shift' 0
  where 
    shift' c d (Var k)
      | k < c = Var k
      | otherwise = Var (k + d)
    shift' c d (Con f as) = Con f (map (shift' c d) as)
    shift' _ _ Bot = Bot
    shift' c d (Abs l e) = Abs l (shift' (c+1) d e)
    shift' c d (App e1 e2) = App (shift' c d e1) (shift' c d e2)
    shift' c d (Cond e cs) = Cond (shift' c d e) [(g, shift' c d e') | (g,e') <- cs]
    shift' c d (Fix e) = Fix (shift' c d e)
      
-- | @subst j e1 e2 == e2[j <- e1]@
subst :: Int -> Exp l -> Exp l -> Exp l
subst j e (Var k)
  | k == j = e
  | otherwise = Var k
subst j e (Con f as) = Con f (map (subst j e) as)
subst _ _ Bot = Bot
subst j e (Abs l f) = Abs l (subst (j+1) (shift 1 e) f)
subst j e (App f1 f2) = App (subst j e f1) (subst j e f2)
subst j e (Cond f cs) = Cond (subst j e f) [(g, subst j e e') | (g,e') <- cs]
subst j e (Fix f) = Fix (subst j e f)

-- * steps
beta :: Exp l -> Maybe (Exp l)
beta (App (Abs _ e) f) = Just (shift (-1) (subst 0 (shift 1 f) e))
beta _ = Nothing

-- cond g(e1,...,en) [... (g,\a1...an.e) ...] -> e{e1/a1,...,en/an}
cond :: Exp l -> Maybe (Exp l)
cond (Cond (Con g es) cs) =
  case lookup g cs of
   Nothing -> Just Bot
   Just eg -> foldM (\ e ei -> beta (App e ei)) eg es
cond _ = Nothing


-- fix(\e.f) --> f{(\z.fix(\e.f) z) / e}
fixCBV :: Exp l -> Maybe (Exp l)
fixCBV f@(Fix e) = beta (App e (delay f))
  where delay f' = Abs Nothing (App (shift 1 f') (Var 0))
fixCBV _ = Nothing

-- * call-by-value
cbvWith :: (Exp l -> Maybe (Exp l)) -> Exp l -> Maybe (Exp l)
cbvWith stp e = ctxt e <|> stp e
  where       
    ctxt (App e1 e2) = do
      [f1,f2] <- cbvl [e1,e2]
      return (App f1 f2)
    ctxt (Con g es) = Con g <$> cbvl es
    ctxt (Cond f cs) = do
      f' <- cbvWith stp f
      return (Cond f' cs)
    ctxt _ = Nothing

    cbvl [] = Nothing
    cbvl (f:fs) =
      case cbvWith stp f of
       Just f' -> Just (f':fs)
       Nothing -> (:) f <$> cbvl fs

cbv :: Exp l -> Maybe (Exp l)
cbv = cbvWith (\ e -> beta e <|> fixCBV e <|> cond e)

nf :: (Exp l -> Maybe (Exp l)) -> Exp l -> Exp l
nf rel e = maybe e (nf rel) (rel e)





