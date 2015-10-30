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
  -- * Strategies
  , simplify
  , simplifyATRS
  , cfa
  , toTRS
) where

import           Control.Applicative (empty)
import qualified Data.Map as Map
import Data.List (nub)
import Data.Maybe (mapMaybe)
import qualified Data.Rewriting.Applicative.Rule as R
import           Data.Rewriting.Applicative.Term
import           Hoca.PCF.Core (Program, TypedProgram)
import qualified Hoca.PCF.Core.DMInfer as DMInfer
import           Hoca.PCF.Sugar.Types (Context)
import           Hoca.Problem
import           Hoca.Data.MLTypes
import           Hoca.Strategy
import           Hoca.Transform.Defunctionalize (defunctionalize)
import           Hoca.Data.Symbol (Symbol(..))
import           Hoca.Transform.Inlining
import           Hoca.Transform.Instantiate
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
  replace _ trl ss = Just [ (trl { theRule = R.mapSides compressTerm (theRule trl)} ,ss)]
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


-- strategies

simplifyATRS :: Problem Symbol Int :=> Problem Symbol Int
simplifyATRS =
  try (exhaustive (rewrite (withRule lambdaRule)))
  >=> try (exhaustive (inline (withRule caseRule)))
  >=> try usableRulesSyntactic

simplify :: (Eq f, Ord f) => Problem f Int :=> Problem f Int
simplify = 
  try (exhaustive (inline (withRule leafRule)) >=> try usableRulesSyntactic) 
  >=> try (exhaustive ((inline decreasing <=> cfaUR) >=> try usableRulesSyntactic))
  >=> try compress
  where
    cfaUR = instantiate refineND

cfa :: Ord f => Problem f Int :=> Problem f Int
cfa = instantiate (refineND `orRefine` refineHOVars) where

toTRS :: Problem Symbol Int :=> Problem TRSSymbol Int
toTRS = try cfa >=> try usableRulesSyntactic >=> uncurried >=> try usableRulesSyntactic
