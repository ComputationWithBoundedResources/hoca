-- | 

module Hoca.Problem.Ops (
  -- * Problems     
  rules
  , fromRules
  , fromGraph
  , rulesEnum
  , size
  , funs
  , leftHandSides
  , rightHandSides
  , renameRules
  -- ** Call Graph Operations
  , rule
  , toAssocList
  , indexOf
  , cgSuccs
  , cgPreds
  -- , usable
  , usableIdx
  -- , isRecursive
  -- , isRecursiveIdx
  -- ** Traversal and Modification
  , restrictIdx
  , removeUnusedRules
  , removeInstances  
  , replaceRules
  , replaceRulesIdx
  , withEdges
  , withEdgesIdx
  -- , modifyMains
  , modifySignature
  -- * Typed Rules
  , renameTRule
  , (|-)
  , tvsFromTRule
  -- * Parsing
 , fromFile
) where


import           Control.Arrow (first, second)
import           Control.Applicative (empty, Alternative)
import           Control.Monad (foldM)
import Control.Monad.State (evalState,get, put)
import qualified Data.IntMap as IMap
import qualified Data.Map as Map
import  Data.List ((\\),nub)
import qualified Data.IntSet as ISet
import           Data.Maybe (listToMaybe)
import qualified Data.Rewriting.Applicative.Rule as R
import qualified Data.Rewriting.Applicative.Problem as P
import qualified Data.Rewriting.Applicative.Term as T
import qualified Data.Rewriting.Applicative.Rules as RS
import           Hoca.Data.MLTypes (Signature, Type, MLType(..),TypeVariable,tvs,decl,TypeDecl(..), signatureToList, TypeDeclaration(..))
import           Hoca.Problem.Type
import           Hoca.Data.Symbol
import           Hoca.Problem.DMInfer (TypingError (..),infer)
import           Hoca.Utils (runVarSupply, fresh)
import qualified Text.PrettyPrint.ANSI.Leijen as PP

renameTRule :: (v -> v') -> TRule f v -> TRule f v'
renameTRule f tr = 
  TRule { theRule = R.mapSides (T.amap id f) (theRule tr) 
        , theEnv = map (first f) (theEnv tr)
        , theType = theType tr }

tvsFromTRule :: TRule f v -> [TypeVariable]
tvsFromTRule trl = concatMap tvs (theType trl : map snd (theEnv trl))

(|-) :: TypingEnv v -> (R.ARule f v, Type) -> TRule f v
env |- (rl,tp) = TRule rl env tp


size :: Problem f v -> Int
size = IMap.size . ruleGraph
  
rules :: Problem f v -> [TRule f v]
rules = map fst . IMap.elems . ruleGraph

rulesEnum :: Problem f v -> [(Int, TRule f v)]
rulesEnum = IMap.toList . IMap.map fst . ruleGraph

fromRules :: (Ord f, Ord v) => StartTerms f -> Signature f -> [TRule f v] -> Problem f v
fromRules sts sig rs = 
  Problem { ruleGraph = IMap.map (\ r -> (r,is)) (IMap.fromList irs)
          , startTerms = sts
          , signature = sig } where
    irs = zip [1..] rs
    is = ISet.fromList (map fst irs)

fromGraph :: StartTerms f -> Signature f -> [(Int,TRule f v)] -> (Int -> Int -> Bool) -> Problem f v
fromGraph sts sig ns edgeP = 
  Problem { ruleGraph = IMap.fromList [ (n, (trl, ISet.fromList [ m | m <- idxs, edgeP n m]))
                                      | (n,trl) <- ns ] 
          , startTerms = sts                                      
          , signature = sig } where
    idxs = map fst ns

funs :: Problem f v -> [(f,Int)]
funs rs = RS.funs ((R.mapSides T.withArity . theRule) `map` rules rs)
          
leftHandSides :: Problem f v -> [T.ATerm f v]
leftHandSides = map (R.lhs . theRule) . rules

rightHandSides :: Problem f v -> [T.ATerm f v] 
rightHandSides = map (R.rhs . theRule) . rules 

modifySignature :: (Signature f -> Signature f) -> Problem f v -> Problem f v 
modifySignature f p = p { signature = f (signature p)}

-- modifyMains :: ([f] -> [f]) -> Problem f v -> Problem f v 
-- modifyMains f p = p { mains = f (mains p)}

---------------------------------------------------------------------- 
-- graph ops
---------------------------------------------------------------------- 

modifyRuleGraph :: (RuleGraph f v -> RuleGraph f v') -> Problem f v -> Problem f v'
modifyRuleGraph f p = p { ruleGraph = f (ruleGraph p) }

restrictIdx :: [Int] -> Problem f v -> Problem f v
restrictIdx ixs = modifyRuleGraph restrict where
  restrict rg = IMap.fromList [ (i,(rl, ss `ISet.intersection` ixss))
                              | (i,(rl,ss)) <- IMap.toList rg
                              , i `ISet.member` ixss]
  ixss = ISet.fromList ixs


indexOf :: (Eq f, Eq v) => Problem f v -> R.ARule f v -> Maybe Int
indexOf p rl = listToMaybe [ i | (i,(rl',_)) <- IMap.toList (ruleGraph p), rl == theRule rl']

rule :: Problem f v -> Int -> Maybe (TRule f v)
rule p i = fst <$> IMap.lookup i (ruleGraph p)

cgSuccs :: Problem f v -> Int -> [Int]
cgSuccs p i = maybe [] (ISet.toList . snd) (IMap.lookup i (ruleGraph p))

cgPreds :: Problem f v -> Int -> [Int]
cgPreds p i = IMap.foldWithKey collect [] (ruleGraph p) where
  collect j (_,ss) preds
    | i `ISet.member` ss = j : preds
    | otherwise = preds

usableIdx :: Problem f v -> [Int] -> [Int]
usableIdx p initial = walk (concatMap (cgSuccs p) initial) [] where
  walk [] seen = seen
  walk (i:is) seen
    | i `elem` seen = walk is seen
    | otherwise = walk (cgSuccs p i ++ is) (i : seen)

-- usable :: (Eq f, Eq v) => Problem f v -> [R.ARule f v] -> [(Int, R.ARule f v)]
-- usable p rs = [(i,r) | i <- usableIdx p (catMaybes [indexOf p rl | rl <- rs])
--                      , let Just r = rule p i ]


-- isRecursive :: (Eq f, Eq v) => Problem f v -> R.ARule f v -> Bool
-- isRecursive p rl = maybe False (isRecursiveIdx p) (indexOf p rl)

-- isRecursiveIdx :: Problem f v -> Int -> Bool
-- isRecursiveIdx p i = i `elem` usableIdx p [i]

---------------------------------------------------------------------- 
-- auxiliary
---------------------------------------------------------------------- 


toAssocList :: Problem f v -> [(TRule f v, Int, [Int])]
toAssocList p = [(i,r,ISet.toList ss) | (r,(i,ss)) <- IMap.toList (ruleGraph p)]

removeUnusedRules :: Eq f => Problem f v -> Problem f v
removeUnusedRules p = modifyRuleGraph (IMap.filterWithKey (\ k _ ->  (k `elem` used))) p where
  used = initial ++ usableIdx p initial
  initial = [i | (i,(r,_)) <- IMap.toList (ruleGraph p)
               , case T.atermM (R.lhs (theRule r)) of
                  Just (T.TFun f _) -> f `elem` defs (startTerms p)
                  _ -> False ]
                  
removeInstances :: (Ord f, Ord v) => Problem f v -> Problem f v
removeInstances p = modifyRuleGraph remv p where 
  rs = map (second theRule) (rulesEnum p)
  remv rg = foldl removeInstance rg insts
  insts = [ (i,j) | (i,ri) <- rs, (j,rj) <- rs
                  , i /= j, ri `R.isInstanceOf` rj
                  , i < j || not (rj `R.isInstanceOf` ri) ]
  removeInstance m (i,j) = IMap.map relink (IMap.delete i m) where
    relink (rl,ss)
      | ISet.member i ss = (rl,ISet.insert j (ISet.delete i ss))
      | otherwise = (rl,ss)

withEdges :: Eq f => (TRule f v -> TRule f v -> Bool) -> Problem f v -> Problem f v
withEdges edgeP = removeUnusedRules . modifyRuleGraph we where
  we rg = IMap.map f rg where
    f (r,ss) = (r, ISet.filter (isEdge r) ss)
    isEdge r i = maybe False (edgeP r . fst) (IMap.lookup i rg)


withEdgesIdx :: Eq f => (Int -> Int -> Bool) -> Problem f v -> Problem f v
withEdgesIdx edgeP = removeUnusedRules . modifyRuleGraph (IMap.mapWithKey f) where
  f i (r,ss) = (r, ISet.filter (edgeP i) ss)


renameRules :: Ord v => Problem f v -> Problem f Int 
renameRules p = p { ruleGraph = IMap.map (first renameTRl) (ruleGraph p) }  where
    renameTRl trl = flip evalState (Map.empty,0) $ do 
      rl <- renameRl (theRule trl)
      env <- renameEnv (theEnv trl)
      return trl { theEnv = env, theRule = rl }
    renamed v = do 
      (m,i) <- get
      case Map.lookup v m of 
        Nothing -> put (Map.insert v (i+1) m, i+1) >> return (i+1)
        Just j -> return j
    renameEnv = mapM (\ (v,t) -> (, t) <$> renamed v)
    renameRl rl = R.Rule <$> renameTerm (R.lhs rl) <*> renameTerm (R.rhs rl)
    renameTerm (T.Var v) = T.Var <$> renamed v
    renameTerm (T.Fun f ts) = T.Fun f <$> mapM renameTerm ts


---------------------------------------------------------------------- 
-- traversal
---------------------------------------------------------------------- 

replaceRulesIdx :: (Alternative m, Ord f, Ord v) => (Int -> TRule f v -> [Int] -> Maybe [(TRule f v, [Int])]) -> Problem f v -> m (Problem f v)
replaceRulesIdx m p = toProblem (runVarSupply (foldM f (False,[]) (IMap.toList (ruleGraph p))))
  where
    f (changed,l) (i,(r,ISet.toList -> ss)) = 
      case m i r ss of
       Nothing -> do
         j <- fresh
         return (changed, (i, [(j,r,ss)]):l)
       Just rs -> do
         ids <- mapM (const fresh) rs
         return (True, (i, [ (j,r',ss') | (j,(r',ss')) <- zip ids rs ]):l)

    toProblem (False,_) = empty
    toProblem (True,l) = pure (removeUnusedRules (modifyRuleGraph (const rg) p))
       where
        rg = foldl ins IMap.empty (concatMap snd l)
        ins is (j,r,ss) = IMap.insert j (r, newSuccs ss) is
        newSuccs = foldl (\ ss' s -> newIds s `ISet.union` ss') ISet.empty
        newIds i = 
          case lookup i l of
           Nothing -> ISet.empty
           Just ers -> ISet.fromList [ j | (j,_,_) <- ers]

replaceRules :: (Alternative m, Ord f, Ord v) => (TRule f v -> Maybe [(TRule f v, [Int])]) -> Problem f v -> m (Problem f v)
replaceRules f = replaceRulesIdx (\ _ r _ -> f r)

---------------------------------------------------------------------- 
-- parsing
---------------------------------------------------------------------- 

data FromFileError = NoParse P.ProblemParseError
                   | NoType (TypingError TRSSymbol String)

instance PP.Pretty P.ProblemParseError where
    pretty err = PP.text "Error parsing file, problem is:"
                 PP.<$$> pp err 
        where pp (P.UnknownParseError str) = PP.text str
              pp (P.UnsupportedStrategy str) = PP.text "Unsupported strategy" 
                                               PP.<+> PP.squotes (PP.text str)
              pp (P.UnsupportedDeclaration str) = PP.text "Unsupported declaration" 
                                                  PP.<+> PP.squotes (PP.text str)
              pp (P.FileReadError _) = PP.text "Error reading file"
              pp (P.SomeParseError e) = PP.text (show e)
              
instance PP.Pretty FromFileError where
    pretty (NoParse err) = PP.pretty err
    pretty (NoType err) = PP.pretty err    
    

fromFile :: FilePath -> IO (Either FromFileError (Problem TRSSymbol Int))
fromFile fp = 
  either (Left . NoParse) problemFromRules <$> P.fromFile fp (`elem` applys)
    where       
      applys = ["@",".","app"]
      
      toSym = flip TRSSymbol 0
      
      problemFromRules = mkProblem . RS.amap toSym id . P.allRules . P.rules
      mkProblem rs = 
         case infer rs of 
         Left err -> Left (NoType err)
         Right (trls,sig) -> Right (renameRules (fromRules sts sig trls) )
          where
            sts = StartTerms { defs = [d | d <- ds, firstOrder d], constrs = cs }
            fs = nub (RS.funs rs \\ map toSym applys)
            ds = nub [ f | Right (T.Sym f) <- map (T.root . R.lhs) rs]
            hs = [ f | Just f <- map (T.headSymbol . R.lhs) rs]
            cs = fs \\ (ds ++ hs)
            firstOrder (flip decl sig -> Just (ins :~> out)) = allBaseTypes (out:ins) [] where
            firstOrder _ = False

            allBaseTypes [] _ = True
            allBaseTypes ((_ :-> _) : _) _ = False
            allBaseTypes ((TyVar _):ts) seen = allBaseTypes ts seen
            allBaseTypes ((TyCon nm as):ts) seen
                | nm `elem` seen = allBaseTypes (as++ts) (nm:seen)
                | otherwise = allBaseTypes (constrArgs nm ++ as ++ ts) seen

            constrDecls = [ td | (c ::: td) <- signatureToList sig, c `elem` cs ]
            constrArgs nm = concat [ ins | ins :~> TyCon nm' _ <- constrDecls, nm == nm' ]
