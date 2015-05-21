-- | Rewrite Rules in applicative form

module Data.Rewriting.Applicative.Rule (
  -- * Type
  ARule

  -- * specific for rules in applicative form
  , rule
  , funs
  , funsDL
  , mapRule

  -- * re-exported from 'Data.Rewriting.Rule'
  , lhs
  , rhs
  , prettyRule
  , vars
  , varsDL
  , left
  , right
  , rename
  , both  
  , isLinear
  , isLeftLinear
  , isRightLinear
  , isGround
  , isLeftGround
  , isRightGround
  , isErasing
  , isCreating
  , isDuplicating
  , isCollapsing
  , isExpanding
  , isValid
  , isInstanceOf
  , isVariantOf
  ) where

import qualified Data.Rewriting.Applicative.Term as T
import qualified Data.Rewriting.Rule as R

import Data.Rewriting.Rule.Type  (lhs, rhs)
import Data.Rewriting.Rule.Pretty (prettyRule)
import Data.Rewriting.Rule.Ops hiding (funsDL, funs)

-- | applicative rule, over signature @'Data.Rewriting.Applicative.Term.Asym' f@ that contains beside @f@ a dedicated, binary application symbol
type ARule f v = R.Rule (T.ASym f) v

rule :: T.ATerm f v -> T.ATerm f v -> ARule f v
rule = R.Rule

funs :: ARule f v -> [f]
funs = flip funsDL []

funsDL :: ARule f v -> [f] -> [f]
funsDL r = T.funsDL (lhs r) . T.funsDL (rhs r)

mapRule :: (R.Term f v -> R.Term g w) -> R.Rule f v -> R.Rule g w
mapRule f r = R.Rule{ R.lhs = f (R.lhs r), R.rhs = f (R.rhs r) }

