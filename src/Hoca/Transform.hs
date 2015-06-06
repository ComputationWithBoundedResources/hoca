module Hoca.Transform (
  -- * PCF transformations
   inferPCFType
  , defunctionalize
  -- * ATRS simplifications
  -- ** Rule removal simplifications
  , module Hoca.Transform.UsableRules
  , neededRules
  -- ** Instantiation
  , instantiate
  -- ** Inlining
  , module Hoca.Transform.Inlining
  -- ** Uncurrying  
  , module Hoca.Transform.Uncurry
  -- * Misc
  , compress
  -- * Combinators
  , module Hoca.Strategy
) where

import           Control.Applicative (empty)
import qualified Data.Map as Map
import qualified Data.Rewriting.Applicative.Rule as R
import           Data.Rewriting.Applicative.Term
import           Hoca.Data.MLTypes hiding (instantiate)
import           Hoca.PCF.Core (Program, TypedProgram)
import qualified Hoca.PCF.Core.DMInfer as DMInfer
import           Hoca.PCF.Sugar.Types (Context)
import           Hoca.Problem
import           Hoca.Strategy
import           Hoca.Transform.Defunctionalize (defunctionalize, Symbol(..))
import           Hoca.Transform.Inlining
import           Hoca.Transform.Instantiate (instantiate)
import           Hoca.Transform.Uncurry
import           Hoca.Transform.UsableRules (usableRulesSyntactic, usableRulesDFA)
-- PCF

inferPCFType :: Program Context :=> TypedProgram Context
inferPCFType = either (const empty) pure . DMInfer.infer

-- Simplifications

neededRules :: Ord v => Problem Symbol v :=> Problem Symbol v
neededRules p = replaceRulesIdx (\ _ trl succs -> if needed (theRule trl) then Nothing else Just [(trl,succs)]) p where
  needed rl =
    case headSymbol (R.lhs rl) of
     Just (l@Lambda {}) -> l `elem` createdFuns
     Just (l@Fix {}) -> l `elem` createdFuns
     _ -> True
  createdFuns = foldr funsDL [] (rightHandSides p)


compress :: (Ord f, Ord v) => Problem f v :=> Problem f v
compress p = modifySignature (mapSignature modifyDecl) <$> replaceRulesIdx replace p where
  replace _ trl ss = Just [ (trl { theRule = R.mapRule compressTerm (theRule trl)} ,ss)]
  compressTerm (aterm -> TFun f ts) =
    case Map.lookup f cm of
     Just as -> fun f [compressTerm ti | (Nothing,ti) <- zip as ts ]
     Nothing -> fun f (map compressTerm ts)
  compressTerm (aterm -> t1 :@ t2) = compressTerm t1 `app` compressTerm t2
  compressTerm t = t
  
  cm = foldl ins Map.empty terms where
    ins m (aterm -> TFun f ts) = Map.alter alter f m where
      alter Nothing = Just (map (\ ti -> if isGround ti then Just ti else Nothing) ts)
      alter (Just ts') = Just (zipWith combine ts' ts)
      combine Nothing _ = Nothing
      combine (Just ti') ti
        | ti' == ti && isGround ti = Just ti
        | otherwise = Nothing
    ins m _ = m
  terms = concatMap subterms (leftHandSides p ++ rightHandSides p)
  modifyDecl (f ::: td@(tins :~> tout)) = 
      case Map.lookup f cm of
       Nothing -> td
       Just at -> [ti | (Nothing,ti) <- zip at tins] :~> tout

-- removeUnusedRules :: Problem Symbol v -> Problem Symbol v
-- removeUnusedRules p = p { pRules = IMap.filterWithKey (\ k _ ->  (k `elem` used)) (pRules p) } where
--   used = initial ++ usableIdxs p initial
--   initial = [i | (i,(r,_)) <- IMap.toList (pRules p)
--                , case T.atermM (R.lhs r) of
--                   Just (T.Fun f _) -> unlabeled f == Main
--                   _ -> False ]
   
