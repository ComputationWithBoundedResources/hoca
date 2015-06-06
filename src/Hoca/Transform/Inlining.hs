module Hoca.Transform.Inlining (
  NarrowedRule (..)
  , Narrowing (..)
  -- * Transformations
  , inline
  , rewrite
  -- * Useful predicates
  , complexityPreserving
  , complexityReflecting
  , withRule
  , onRule
  ) where

import qualified Data.Rewriting.Context as C
import Data.Rewriting.Applicative.Rule hiding (rename, vars, isVariantOf, rule)
import qualified Data.Rewriting.Applicative.Rule as R
import Data.Rewriting.Applicative.Term
import qualified Data.Rewriting.Substitution as S
import           Data.Rewriting.Substitution.Unify (unify)
import Hoca.Problem
import Hoca.Strategy
import Control.Monad (guard)
import Hoca.Utils
import Data.Maybe (catMaybes, mapMaybe, listToMaybe, fromMaybe)
import Data.List (nub)
import qualified Data.MultiSet as MS

data NarrowedRule f v1 v2 =
  NarrowedRule {
    narrowedRule :: Rule f v1
    , narrowCtxt :: C.Ctxt f v1
    , narrowSubterm :: Term f v1 
    , narrowings :: [Narrowing f v1 v2]
    } deriving (Show)

data Narrowing f v1 v2 =
  Narrowing {
    narrowingMgu :: S.Subst f (Either v1 v2)
    , narrowedWith :: Rule f v2
    , narrowing :: Rule f (Either v1 v2)
    } deriving (Show)


renameCtx :: (v1 -> v2) -> C.Ctxt f v1 -> C.Ctxt f v2
renameCtx _ C.Hole = C.Hole
renameCtx fn (C.Ctxt f ts1 c ts2) = C.Ctxt f (map (rename fn) ts1) (renameCtx fn c) (map (rename fn) ts2)


narrow :: (Eq f, Ord v1, Ord v2) => Rule f v1 -> [Rule f v2] -> [NarrowedRule f v1 v2]
narrow rl rs = catMaybes [ narrowAt ci ri | (ci,ri) <- contexts (rhs rl), isFun ri ]
  where
    narrowAt ci ri = do
      let ns = mapMaybe (narrowWith ci ri) rs
      guard (not (null ns))
      return NarrowedRule {
        narrowedRule = rl
        , narrowCtxt = ci
        , narrowSubterm = ri
        , narrowings = ns }

    narrowWith ci ri rli = do
        mgu <- unify (rename Left ri) (rename Right (lhs rli))
        let ci' = renameCtx Left ci
            lhs' = S.apply mgu (rename Left (lhs rl))
            rhs' = S.applyCtxt mgu ci' `C.apply` S.apply mgu (rename Right (rhs rli))
        return Narrowing { narrowingMgu = mgu
                         , narrowedWith = rli
                         , narrowing = Rule lhs' rhs'
                         }


-- inline :: (Ord f, Ord v, Num v) => (Problem f v -> NarrowedRule (ASym f) v v -> Bool) -> Problem f v :=> Problem f v
inline sensible p = replaceRulesIdx narrowRule p where
  renameRule = R.rename ren where
     ren (Left v) = v * 2 + 1
     ren (Right v) = v * 2
  
  narrowRule i trl ss = applyNarrowing <$> listToMaybe candidates where
    rl = theRule trl
    rsEnum = [ (theRule trl',j) | j <- cgSuccs p i, let Just trl' = rule p j ]
    rs = map fst rsEnum
    sig = signature p
    candidates = [ ni | ni <- narrow rl rs, complexityReflecting p ni, sensible p ni ]
    applyNarrowing ni = [ (trl', ss ++ cgSuccs p nidx )
                        | n <- narrowings ni
                        , let nidx = fromMaybe err (lookup (narrowedWith n) rsEnum) where err = error "narrow rule id not found"
                        , let trl' = either (\ _-> error ("failed typing " ++ render (renameRule (narrowing n)))) id (inferR sig (renameRule (narrowing n)))
                        ]


--rewrite :: (Ord f, Ord v, Num v) => (Problem f v -> NarrowedRule (ASym f) v v -> Bool) -> Problem f v :=> Problem f v
rewrite sensible = inline sensible' where
  sensible' rs nr = all (\ nw -> lhs (narrowedRule nr) `isVariantOf` lhs (narrowing nw)) (narrowings nr)
                    && sensible rs nr


reducibleVars :: (Ord f, Ord v) => Problem f v -> Narrowing (ASym f) v v -> [v]
reducibleVars p n =
  [ v | v <- nub (vars (lhs rl))
      , any isCall (subterms ( mgu `S.apply` var (Right v))) ]
  where
    rl = narrowedWith n    
    mgu = narrowingMgu n
    isCall (aterm -> TVar _)  = False
    isCall (aterm -> (_ :@ _)) = True
    isCall (aterm -> TFun f _) = f `elem` ds
    isCall _ = error "Hoca.Transform.normalisedVars match failure"
    ds = [ f | TFun f _ <- map aterm (leftHandSides p) ]
    

complexityReflecting :: (Ord f, Ord v) => Problem f v -> NarrowedRule (ASym f) v v -> Bool
complexityReflecting p nr = all redexPreserving (narrowings nr) where
  redexPreserving n = varsMS (lhs rl) == varsMS (rhs rl) where
    rl = narrowedWith n
    varsMS = MS.fromList . filter (`elem` withCall) . vars
    withCall = reducibleVars p n

complexityPreserving :: (Ord f, Ord v) => Problem f v -> NarrowedRule (ASym f) v v -> Bool
complexityPreserving p nr = all redexReflecting (narrowings nr) where
  redexReflecting n = varsMS (rhs rl) `MS.isSubsetOf` varsMS (lhs rl) where
    rl = narrowedWith n
    varsMS = MS.fromList . filter (`elem` withCall) . vars
    withCall = reducibleVars p n


withRule,onRule :: (Problem f v -> ARule f v -> Bool) -> Problem f v -> NarrowedRule (ASym f) v v -> Bool
withRule p rs = all (p rs) . map narrowedWith . narrowings
onRule p rs = p rs . narrowedRule
    
