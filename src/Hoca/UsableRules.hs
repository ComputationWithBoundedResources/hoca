-- | 

module Hoca.UsableRules (
  usableSyms
  , usableRules
  , withUsableRules
  ) where

import qualified Data.Rewriting.Rule as R
import qualified Data.Rewriting.Rules as RS
import qualified Data.Rewriting.Term as T
import           Data.List (partition,union)


ruleDefines :: Eq f => [f] -> R.Rule f v -> Bool
ruleDefines fs = either (const True) (`elem` fs) . T.root . R.lhs

usableSyms :: (Show f, Eq f) => [f] -> [R.Rule f v] -> [f]
usableSyms fs rs = walk (usableSyms' (filter (ruleDefines fs) rs) `union` fs) rs
  where
    usableSyms' = foldr T.funsDL [] . RS.rhss
    walk fs' [] = fs'
    walk fs' rs2 = if null usable then fs' else walk (usableSyms' usable `union` fs') nonusable
      where (usable, nonusable) = partition (ruleDefines fs') rs2

usableRules :: (Show f, Eq f) => [R.Rule f v] -> [R.Rule f v] -> [R.Rule f v]
usableRules rs rs2 = filter (ruleDefines (usableSyms fs rs2)) rs2
  where fs = foldr T.funsDL [] (RS.rhss rs)

withUsableRules :: (Show f, Eq f) => [R.Rule f v] -> [R.Rule f v] -> [R.Rule f v]
withUsableRules rs rs2 = rs ++ usableRules rs rs2
