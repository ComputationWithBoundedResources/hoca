module Hoca.SizeTypes.Infer where

-- TODOS
-- !! check that fvars and bvars are disjoint!!

import           Control.Monad.Except
import           Control.Monad.RWS
import           Data.Map (Map)
import           Data.Maybe (mapMaybe)
import           Data.Rewriting.Applicative.Rule hiding (funs)
import           Data.Rewriting.Applicative.Term hiding (funs)
import qualified Hoca.Data.MLTypes as MLTypes
import           Hoca.Problem.DMInfer (TTerm (..))
import qualified Hoca.Problem.DMInfer as DMInfer
import           Hoca.Problem.Ops
import           Hoca.Problem.Type
import qualified Data.Map as Map
import Hoca.Utils (ppSeq,renderPretty, assertJust, assert, tracePretty)
import Data.List ((\\), nub, intersperse)
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Control.Monad.State (evalStateT)
import qualified GUBS as GUBS
import qualified GUBS.Solver.SMTLib as GUBS

----------------------------------------------------------------------
-- positions in terms and types
----------------------------------------------------------------------

class Position p where
  type Direction p
  posCon   :: [Direction p] -> p
  posDestr :: p -> [Direction p]

emptyPos :: Position p => p
emptyPos = posCon []

posAdd :: Position p => p -> Direction p -> p
posAdd p d = posCon (d : posDestr p)

posToList :: Position p => p -> [Direction p]
posToList = reverse . posDestr

ppPos :: Position p => (Direction p -> PP.Doc) -> p -> PP.Doc
ppPos pp pos = PP.hcat (intersperse PP.dot [ pp i | i <- posToList pos])

-- positions in terms 
----------------------------------------------------------------------
newtype Pos = Pos [Int]  deriving (Eq, Ord, Show)

instance Position Pos where 
  type Direction Pos = Int
  posCon = Pos
  posDestr (Pos ds) = ds

instance Monoid Pos where
  mempty = emptyPos
  mappend p1 p2 = posCon (posDestr p2 ++ posDestr p1)

instance PP.Pretty Pos where
  pretty = ppPos PP.int

-- positions in types
----------------------------------------------------------------------

data TDir = TArg Int | TP | TN deriving (Eq, Ord,Show)
newtype TPos = TPos [TDir] deriving (Eq, Ord, Show)

instance Position TPos where 
  type Direction TPos = TDir
  posCon = TPos
  posDestr (TPos ds) = ds

instance Monoid TPos where
  mempty = emptyPos
  mappend p1 p2 = posCon (posDestr p2 ++ posDestr p1)

instance PP.Pretty TPos where
  pretty = ppPos ppTDir where
    ppTDir (TArg i) = PP.int i
    ppTDir TP = PP.text "P"
    ppTDir TN = PP.text "N"

-- calling contexts

type RuleNum = Int
newtype CallingContext = CallingContext [(RuleNum,Pos)] deriving (Eq, Ord, Show)

instance Position CallingContext where 
  type Direction CallingContext = (RuleNum,Pos)
  posCon = CallingContext
  posDestr (CallingContext ds) = ds

instance PP.Pretty CallingContext where
  pretty (CallingContext []) = PP.text "G"
  pretty (CallingContext l) =
    PP.hcat (PP.punctuate (PP.text "->") [ PP.int i PP.<> PP.text ":" PP.<> PP.pretty pos | (i,pos) <- reverse l])



----------------------------------------------------------------------
-- index terms
----------------------------------------------------------------------

-- better to model with rewriting-library?
type IxVarId = Int

data IxVar = BVar IxVarId | FVar IxVarId deriving (Eq, Ord, Show)

type UniqueFunId = Int

data IxSym f =
  IxSym f CallingContext TPos
  | IxSkolem UniqueFunId
  deriving (Eq, Ord, Show)

data IxTerm f =
  IxZero
  | IxSucc (IxTerm f)
  | IxSum [IxTerm f]
  | IxFun (IxSym f) [IxTerm f]
  | IxVar IxVar
  deriving (Eq, Ord, Show)

data Constraint f = IxTerm f :>=: IxTerm f

fvar :: IxVarId -> IxTerm f
fvar = IxVar . FVar

bvar :: IxVarId -> IxTerm f
bvar = IxVar . BVar

ixZero :: IxTerm f
ixZero = IxZero

ixSucc :: IxTerm f -> IxTerm f
ixSucc = IxSucc

ixSum :: [IxTerm f] -> IxTerm f
ixSum [] = ixZero
ixSum [t] = t
ixSum ts = IxSum ts

indexVars :: IxTerm f -> [IxVarId]
indexVars IxZero = []
indexVars (IxSucc ix) = indexVars ix
indexVars (IxSum ixs) = concatMap indexVars ixs
indexVars (IxFun _ ixs) = concatMap indexVars ixs
indexVars (IxVar (BVar _)) = []
indexVars (IxVar (FVar v)) = [v]

indexSyms :: IxTerm f -> [(IxSym f,Int)]
indexSyms IxZero = []
indexSyms (IxSucc ix) = indexSyms ix
indexSyms (IxSum ixs) = concatMap indexSyms ixs
indexSyms (IxFun f ixs) = (f,length ixs) : concatMap indexSyms ixs
indexSyms (IxVar _) = []


-- pretty printers

prettyFn :: PP.Pretty a => String -> [a] -> PP.Doc
prettyFn n as = PP.text n PP.<> prettyArgLst as

prettyArgLst :: PP.Pretty a => [a] -> PP.Doc
prettyArgLst as = PP.encloseSep PP.lparen PP.rparen PP.comma [PP.pretty ai | ai <- as]

prettyVar :: Int -> PP.Doc
prettyVar i = PP.text "x" PP.<> PP.int i

instance PP.Pretty IxVar where
  pretty (BVar i) = prettyVar i
  pretty (FVar i) = prettyVar i

instance PP.Pretty f => PP.Pretty (IxSym f) where
  pretty (IxSym f cs tpos) =
    PP.pretty f PP.<> ppCs cs PP.<> PP.text "#" PP.<> PP.pretty tpos
    where
      ppCs (CallingContext []) = PP.empty
      ppCs cc = PP.text "#" PP.<> PP.pretty cc
  pretty (IxSkolem i) = PP.text "s_" PP.<> PP.int i

instance PP.Pretty f => PP.Pretty (IxTerm f) where
  pretty IxZero = PP.text "0"
  pretty (IxSucc ix) = prettyFn "s" [ix]
  pretty (IxSum ixs) = prettyFn "sum" ixs
  pretty (IxFun sym as) = PP.pretty sym PP.<> prettyArgLst as
  pretty (IxVar v) = PP.pretty v

instance PP.Pretty f => PP.Pretty (Constraint f) where
  pretty (ix1 :>=: ix2) = PP.hang 2 $ PP.pretty ix1 PP.<+> PP.text ">=" PP.</> PP.pretty ix2


-- substitutions
----------------------------------------------------------------------

type IxSubst f = IxVarId -> IxTerm f -- Invariant: image is free of BVar's 

idSubst :: IxSubst f
idSubst = fvar

substFromList :: [(IxVarId, IxTerm f)] -> IxSubst f
substFromList []           v = fvar v
substFromList ((v,ix):ls)  v' 
  | v == v' = ix
  | otherwise = substFromList ls v'

after :: IxSubst f -> IxSubst f -> IxSubst f
s1 `after` s2 = \ v -> s1 `o` s2 v

class Substitutable c where
  type Image c
  subst_ :: (IxVar -> Image c) -> c -> c

o :: (Substitutable c, Image c ~ IxTerm f) => IxSubst f -> c -> c
o s = subst_ s' where 
  s' (BVar v) = bvar v
  s' (FVar v) = s v
    
inst :: (Substitutable c, Image c ~ IxTerm f) => IxSubst f -> c -> c
inst s = subst_ s' where 
  s' (BVar v) = s v 
  s' (FVar v) = fvar v
  
instance Substitutable (IxTerm f) where
  type Image (IxTerm f) = IxTerm f
  subst_ _ IxZero = IxZero
  subst_ s (IxSucc ix) = IxSucc (subst_ s ix)
  subst_ s (IxSum ixs) = IxSum (map (subst_ s) ixs)
  subst_ s (IxFun f ixs) = IxFun f (map (subst_ s) ixs)
  subst_ s (IxVar v) = s v

----------------------------------------------------------------------
-- size types
----------------------------------------------------------------------

type TypeName = MLTypes.TypeName
type TypeVariable = MLTypes.TypeVariable

data Kind = B | N | P

data SizeType knd ix where 
  TyVar :: TypeVariable -> SizeType knd ix
  TyCon :: TypeName -> ix -> [BaseType ix] -> SizeType knd ix
  TyArr :: NegType ix -> Type ix -> Type ix
  TyQ   :: [IxVarId] -> Type ix -> NegType ix

type BaseType = SizeType 'B
type NegType = SizeType 'N
type Type = SizeType 'P

fromBType :: BaseType ix -> SizeType knd ix
fromBType (TyVar v) = TyVar v
fromBType (TyCon nm ix bs) = TyCon nm ix bs

-- freeVars :: SizeType knd (IxTerm f) -> [IxVarId]
-- freeVars (TyVar _) = []
-- freeVars (TyCon _ ix bs) = indexVars ix ++ concatMap freeVars bs
-- freeVars (TyArr n p) = freeVars n ++ freeVars p
-- freeVars (TyQ _ p) = freeVars p

uncurryUpto :: Type ix -> Int -> Maybe ([NegType ix], Type ix)
uncurryUpto t 0 = Just ([],t)
uncurryUpto (TyArr n t) i
  | i > 0 = do
      (ns,t') <- uncurryUpto t (i - 1)
      return (n:ns,t')
uncurryUpto _ _ = Nothing

curryTpe :: ([NegType ix], Type ix) -> Type ix
curryTpe ([],t) = t
curryTpe (n:ns,t) = TyArr n (curryTpe (ns,t))

simpleTypeOf :: SizeType knd ix -> MLTypes.Type
simpleTypeOf (TyVar v) = MLTypes.TyVar v
simpleTypeOf (TyCon nm _ ts) = MLTypes.TyCon nm (simpleTypeOf `map` ts)
simpleTypeOf (TyArr n p) = simpleTypeOf n MLTypes.:-> simpleTypeOf p
simpleTypeOf (TyQ  _ t) = simpleTypeOf t

instance Substitutable (SizeType knd (IxTerm f)) where
  type Image (SizeType knd (IxTerm f)) = IxTerm f
  subst_ _ (TyVar v) = TyVar v
  subst_ s (TyCon nm ix ns) = TyCon nm (subst_ s ix) (map (subst_ s) ns)
  subst_ s (TyArr n p) = TyArr (subst_ s n) (subst_ s p)
  subst_ s (TyQ vs p) = TyQ vs (subst_ s' p) where
    s' (BVar v) | v `elem` vs = IxVar (BVar v)
    s' v = s v
    
matrix :: NegType (IxTerm f) -> Tc ctx f v ([IxVarId], Type (IxTerm f))
matrix (TyVar v) = return ([],TyVar v)
matrix (TyCon nm ix bs) = return ([], TyCon nm ix bs)
matrix (TyQ vs t) = do
  vs' <- replicateM (length vs) uniqueIxVar
  return (vs', inst (substFromList (zip vs (fvar `map` vs'))) t)

prettyType :: (ix -> PP.Doc) -> SizeType knd ix -> PP.Doc
prettyType = ppTpe id
  where
    ppTpe :: (PP.Doc -> PP.Doc) -> (ix -> PP.Doc) -> SizeType knd ix -> PP.Doc
    ppTpe _ _ (TyVar i) = PP.text ("'" ++ MLTypes.variableNames !! i)
    ppTpe _ pix (TyCon nm ix bs) = ppArgs bs PP.<+> PP.text nm PP.<> ppIx
      where
        ppIx = PP.text "_" PP.<> PP.braces (pix ix)
        ppArgs [] = PP.empty
        ppArgs [t] = ppTpe id pix t
        ppArgs ts = PP.parens (ppSeq PP.comma [ ppTpe id pix t | t <- ts])
    ppTpe par pix (TyArr n t) =
      par (PP.hang 2 $
           ppTpe PP.parens pix n PP.<+> PP.text "->" PP.</> ppTpe id pix t)
    ppTpe par pix (TyQ qvs t) = par (PP.hang 2 $ ppQual qvs PP.</> ppTpe id pix t) where
        ppQual [] = PP.empty
        ppQual vs = PP.text "forall" PP.<+> ppSeq PP.space [ PP.pretty (BVar v) | v <- vs] PP.<> PP.text "."

instance PP.Pretty ix => PP.Pretty (SizeType knd ix) where
  pretty = prettyType PP.pretty

----------------------------------------------------------------------
-- type inference
----------------------------------------------------------------------

newtype Signature f ix = Signature { sigToMap :: Map f (NegType ix) }

extendSig :: Ord f => f -> NegType ix -> Signature f ix -> Signature f ix
extendSig f n (Signature m) = Signature (Map.insert f n m)

type Env v f = Map v (NegType (IxTerm f))

data TypingError f v = 
  IllformedLhs (ATerm f v)
  | IllformedRhs (ATerm f v)
  | UnExpectedNumArgs f (Type (IxTerm f)) Int
  | DeclarationMisMatch (ATerm f v) (NegType (IxTerm f))
  | IllformedConstructorDeclaration f
  | NonBasicConstructor f
  | DeclarationMissing f
  | ConstraintsUnsolvable

instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (TypingError f v) where
  pretty err = PP.text "Error in inference of size types. "
               PP.<$$> pp err
    where
      pp (IllformedLhs t) =
        PP.hang 2 (PP.text "Illformed left-hand side encountered:" PP.</> prettyATerm t)
      pp (IllformedRhs t) =
        PP.hang 2 (PP.text "Illformed right-hand side encountered:" PP.</> prettyATerm t)
      pp (UnExpectedNumArgs f ntpe i) =
        PP.hang 2 (PP.text "The function" PP.<+> PP.squotes (PP.pretty f)
                   PP.</> PP.text "is applied to" PP.<+> PP.int i PP.<+> PP.text "arguments,"
                   PP.</> PP.text "which is incompatible with its type "  PP.<+> PP.squotes (PP.pretty ntpe) )
      pp (DeclarationMisMatch t n) =
        PP.hang 2 (PP.text "Error in construction of footprint."
                   PP.</> PP.text "The term" PP.<+> PP.squotes (prettyATerm t)
                   PP.</> PP.text "cannot be given the size-type"
                   PP.<+> PP.squotes (PP.pretty n))
      pp (IllformedConstructorDeclaration c) =
        PP.text "Illformed constructor-declaration for constructor" PP.<+> PP.squotes (PP.pretty c) PP.<+> PP.text "encountered."
      pp (NonBasicConstructor c) =
        PP.text "Non-basic constructor" PP.<+> PP.squotes (PP.pretty c) PP.<+> PP.text "encountered."
      pp (DeclarationMissing f) =
        PP.text "Type-declaration of symbol" PP.<+> PP.squotes (PP.pretty f) PP.<+> PP.text "missing."
      pp ConstraintsUnsolvable =
        PP.text "The resulting constraints could not be resolved."
        
  
data TcState f = TcState { 
  stQueue :: [(f, CallingContext, NegType (IxTerm f), Signature f (IxTerm f))]
  , stSig :: Signature (f,CallingContext) (IxTerm f)
  , stDefineds :: [f]
  , stUnique :: Int }

data TypingContext f v = TypingContext {
  tcEnv :: Env v f
  , tcFreeIxVars :: [IxVarId]
  , tcCallingContext :: CallingContext
  , tcSignature :: Signature f (IxTerm f)
  , tcRule :: ARule f v -- for error messages
  , tcRuleNum :: Int
  }

data TcContexts = GlobalCtx | RuleCtx

data Context ctx f v where
  GlobalC :: MLTypes.Signature f -> Context 'GlobalCtx f v
  RuleC   :: MLTypes.Signature f -> TypingContext f v -> Context 'RuleCtx f v

newtype Tc ctx f v a =
  Tc { runTc_ :: RWST (Context ctx f v) [Constraint f] (TcState f) (ExceptT (TypingError f v) IO) a }
  deriving (Applicative, Functor, Monad
            , MonadState (TcState f)
            , MonadReader (Context ctx f v)
            , MonadWriter [Constraint f]
            , MonadIO 
            , MonadError (TypingError f v))

runTc :: Eq f => Tc 'GlobalCtx f v1 a -> Problem f v -> ExceptT (TypingError f v1) IO (a, [Constraint f])
runTc m prob = evalRWST (runTc_ m) (GlobalC sig) initialState
  where
    initialState = TcState { stQueue = [], stSig = Signature Map.empty, stUnique = 0, stDefineds = ds }
    sig = signature prob
    ds = nub (mapMaybe headSymbol (leftHandSides prob))


-- operations in all contexts
----------------------------------------------------------------------

uniqueID :: Tc ctx f v IxVarId
uniqueID = do
  s <- get
  let i = stUnique s
  put s { stUnique = i + 1}
  return i
  
uniqueIxVar :: Tc ctx f v IxVarId
uniqueIxVar = uniqueID

uniqueFunId :: Tc ctx f v UniqueFunId
uniqueFunId = uniqueID

uniqueTyVar :: Tc ctx f v TypeVariable
uniqueTyVar = uniqueID

isDefined :: Eq f => f -> Tc ctx f v Bool
isDefined f = elem f <$> stDefineds <$> get

getStSignature :: Tc ctx f v (MLTypes.Signature f)
getStSignature = sigFromCtx <$> ask
  where
    sigFromCtx :: Context ctx f v -> MLTypes.Signature f
    sigFromCtx (RuleC sig _) = sig
    sigFromCtx (GlobalC sig) = sig

getStDeclaration :: Ord f => f -> Tc ctx f v MLTypes.TypeDecl
getStDeclaration f = do
  sig <- getStSignature
  assertJust (DeclarationMissing f) (MLTypes.decl f sig)

getDeclaration :: Ord f => f -> CallingContext -> Tc 'RuleCtx f v (Maybe (NegType (IxTerm f)))
getDeclaration f cs = do
  Signature localSig <- tcSignature <$> getTypingContext
  Signature globalSig <- stSig <$> get
  return (Map.lookup f localSig `mplus` Map.lookup (f,cs) globalSig)

  

-- operations in rule contexts
----------------------------------------------------------------------

withTypingContext :: TypingContext f v -> Tc 'RuleCtx f v a -> Tc 'GlobalCtx f v a
withTypingContext tc m = do
  s <- get
  GlobalC sig <- ask
  res <- liftIO (runExceptT (runRWST (runTc_ m) (RuleC sig tc) s))
  case res of
    Left err -> throwError err
    Right (a,s',w') -> put s' >> tell w' >> return a 

withSkolemVars :: [IxVarId] -> Tc 'RuleCtx f v a -> Tc 'RuleCtx f v a
withSkolemVars vs = local (\ (RuleC sig tc) -> RuleC sig tc { tcFreeIxVars = vs ++ tcFreeIxVars tc} )

getTypingContext :: Tc 'RuleCtx f v (TypingContext f v)
getTypingContext = do {RuleC _ tc <- ask; return tc }


lookupEnv :: Ord v => v -> Tc 'RuleCtx f v (NegType (IxTerm f))
lookupEnv v = do
  mt <- Map.lookup v <$> tcEnv <$> getTypingContext
  rl <- tcRule <$> getTypingContext
  assertJust (IllformedRhs (rhs rl)) mt

getCallingContext :: Pos -> Tc 'RuleCtx f v CallingContext
getCallingContext pos = do
  rlNum <- tcRuleNum <$> getTypingContext
  cs <- tcCallingContext <$> getTypingContext
  return (cs `posAdd` (rlNum,pos))


-- creation of declarations, footprint
-----------------------------------------------------------------------

scoped :: MonadState s m => m a -> m a
scoped m = do { s <- get; a <- m; put s; return a }

toVar :: MLTypes.MLType v -> Maybe v
toVar (MLTypes.TyVar v) = Just v
toVar _ = Nothing

frId :: MonadState ([Int],Int) m => m Int
frId = do
  (vs,i) <- get
  put (i:vs,i+1)
  return i

usedIds :: MonadState ([Int],Int) m => m [Int]
usedIds = reverse <$> fst <$> get

-- TODO: allow type arguments in constructors
freshConstructorDeclaration :: f -> MLTypes.Type -> Tc ctx f v (NegType (IxTerm f))
freshConstructorDeclaration c stpe = flip evalStateT ([],0) $ do
  tpe <- annotate stpe
  vs <- usedIds
  return (TyQ vs tpe)
  where
    annotateN (MLTypes.TyVar v) = return (TyVar v)
    annotateN (MLTypes.TyCon nm ts) = 
      TyCon nm <$> (bvar <$> frId) <*> mapM annotateN ts
    annotateN _ = throwError (NonBasicConstructor c)

    annotate (MLTypes.TyVar v) = return (TyVar v)
    annotate (MLTypes.TyCon nm ts) = do
      vs <- lift (assertJust (IllformedConstructorDeclaration c) (mapM toVar ts))
      ix <- ixSucc <$> ixSum <$> map bvar <$> usedIds
      return (TyCon nm ix (TyVar `map` vs))
    annotate (t1 MLTypes.:-> t2) = 
      TyArr <$> (fromBType <$> annotateN t1) <*> annotate t2


freshFunctionDeclaration :: f -> CallingContext -> Int -> MLTypes.Type -> Tc ctx f v (NegType (IxTerm f))
freshFunctionDeclaration f cs k stpe = flip evalStateT ([],k) $ do
  t <- annotateT emptyPos stpe
  used <- usedIds
  return (TyQ (vs ++ used) t)

  where
    vs = [0..k-1]
    annotateN tpos t@(_ MLTypes.:-> _) = scoped $ do
      used <- usedIds
      tpe <- annotateT tpos t
      bvs <- usedIds
      return (TyQ (bvs \\ used) tpe)
    annotateN _ t = fromBType <$> annotateBaseN t
    
    annotateT tpos (t1 MLTypes.:-> t2) = do
      n <- annotateN (tpos `posAdd` TN) t1
      t <- annotateT (tpos `posAdd` TP) t2
      return (TyArr n t)
    annotateT tpos t = fromBType <$> annotateBaseP tpos t

    annotateBaseN (MLTypes.TyVar v) = return (TyVar v)
    annotateBaseN (MLTypes.TyCon nm ts) = do
      bv <- bvar <$> frId
      TyCon nm bv <$> mapM annotateBaseN ts
    annotateBaseN _ = throwError (NonBasicConstructor f)

    annotateBaseP _    (MLTypes.TyVar v) = return (TyVar v)
    annotateBaseP tpos (MLTypes.TyCon nm ts) = do
      used <- usedIds
      let ix = IxFun (IxSym f cs tpos) [bvar v | v <- vs ++ used]
      TyCon nm ix <$> sequence [ annotateBaseP  (tpos `posAdd` TArg i) bi
                               | (i,bi) <- zip [0..] ts ]
    annotateBaseP _ _ = throwError (NonBasicConstructor f)


freshDeclaration :: Ord f => f -> CallingContext -> [IxVarId] -> Signature f (IxTerm f) -> MLTypes.Type -> Tc ctx f v (NegType (IxTerm f))
freshDeclaration f cs freeIxVars localSig stpe = do
  defP <- isDefined f
  if defP
   then do
    n <- freshFunctionDeclaration f cs (length freeIxVars) stpe
    modify $ \ st -> st { stQueue = (f,cs,n,extendSig f n localSig):stQueue st
                        , stSig = extendSig (f,cs) n (stSig st) }
    return n
   else do
    n <- freshConstructorDeclaration f stpe
    modify $ \ st -> st { stSig = extendSig (f,cs) n (stSig st) }
    return n
      
declarationOf :: Ord f => f -> MLTypes.Type -> CallingContext -> Tc 'RuleCtx f v (NegType (IxTerm f))
declarationOf f stpe cs = do
  localSig <- tcSignature <$> getTypingContext
  ixvs <- tcFreeIxVars <$> getTypingContext 
  getDeclaration f cs >>= maybe (freshDeclaration f cs ixvs localSig stpe) return
        

footprint :: (Ord v, Ord f) => ATerm f v -> NegType (IxTerm f) -> Tc ctx f v ([IxVarId], Env v f, Type (IxTerm f))
footprint thelhs declTpe = 
  case aform thelhs of
  Just (Fun (Sym _) ts, as) -> do
    (fvs,tpe) <- matrix declTpe
    (inTps,retTpe) <- assertJust (DeclarationMisMatch thelhs declTpe) (uncurryUpto tpe (length ts + length as))
    (s,env) <- run idSubst [] (zip (ts ++ as) inTps)
    return ( concatMap (indexVars . s) fvs
           , Map.fromList [ (v, s `o` p) | (v,p) <- env ]
           , s `o` retTpe )
  
  _ -> throwError (IllformedLhs thelhs)
  where
    run s env [] = return (s,env)
    run s env ((arg,argTpe):targs) = do 
      let env' = case arg of {Var v -> (v,argTpe):env; _ -> env }
      (s',targs') <- spezialisePattern arg argTpe
      run (s' `after` s) env' (targs' ++ targs)

    spezialisePattern (Var _) _ = return (idSubst,[])
    spezialisePattern (Fun (Sym c) ts) (TyCon nm (IxVar (FVar iv)) bs) = do
      sdecl <- getStDeclaration c
      case sdecl of 
        ins MLTypes.:~> MLTypes.TyCon nm' (mapM toVar -> Just vs) -> do          
          assert (IllformedConstructorDeclaration c) (nm == nm' && length vs == length bs)
          argTps <- (liftM fromBType . instantiateSkeleton (zip vs bs)) `mapM` ins
          return ( substFromList [(iv,ixSucc (ixSum (argSize `mapMaybe` argTps)))]
                     , zip ts argTps)
        _ -> throwError (IllformedConstructorDeclaration c)
      where 
        argSize (TyCon _ ix _) = Just ix
        argSize _ = Nothing
        instantiateSkeleton subst (MLTypes.TyVar v) =
          assertJust (IllformedConstructorDeclaration c) (lookup v subst) 
        instantiateSkeleton subst (MLTypes.TyCon m as) = do 
            v <- uniqueIxVar
            ps <- instantiateSkeleton subst `mapM` as
            return (TyCon m (fvar v) ps)
        instantiateSkeleton _ _ =  throwError (NonBasicConstructor c)
    spezialisePattern (Fun (Sym c) _)  _ = throwError (IllformedConstructorDeclaration c)
    spezialisePattern _                _ = throwError (IllformedLhs thelhs)


-- inference
-----------------------------------------------------------------------

subtypeOf :: (Eq f) => Type (IxTerm f) -> Type (IxTerm f) -> Tc ctx f v ()
subtypeOf = subtypeOf_

subtypeOf_ :: (Eq f) => SizeType knd (IxTerm f) -> SizeType knd (IxTerm f) -> Tc ctx f v ()
TyVar a `subtypeOf_` TyVar b | a == b = 
  return ()
TyCon nm1 ix1 bs1 `subtypeOf_` TyCon nm2 ix2 bs2 | nm1 == nm2 = do
  unless (ix1 == ix2) (tell [ix2 :>=: ix1])
  sequence_ [ b1 `subtypeOf_` b2 | (b1,b2) <- zip bs1 bs2]
TyArr n1 t1 `subtypeOf_` TyArr n2 t2 = do
  n2 `subtypeOf_` n1
  t1 `subtypeOf_` t2
TyQ vs1 t1 `subtypeOf_` TyQ vs2 t2  | length vs1 == length vs2 = do
  vs <- replicateM (length vs1) (fvar <$> uniqueIxVar)
  let t1' = inst (substFromList (zip vs1 vs)) t1 
  let t2' = inst (substFromList (zip vs2 vs)) t2
  t1' `subtypeOf_` t2'
_ `subtypeOf_` _  = error $ "subtypeOf_: comparing incompatible types:\n"

instantiateQ :: NegType (IxTerm f) -> Tc 'RuleCtx f v (Type (IxTerm f))
instantiateQ (TyVar v) = return (TyVar v)
instantiateQ (TyCon nm ix ns) = return (TyCon nm ix ns)
instantiateQ (TyQ vs t) = do 
  s <- substFromList <$> sequence [ (,) v <$> uniqueSkolemTerm | v <- vs]
  return (inst s t)
  where
    uniqueSkolemTerm = IxFun <$> (IxSkolem <$> uniqueFunId)
                             <*> (map fvar <$> tcFreeIxVars <$> getTypingContext)

check :: (Ord v, Ord f) => Pos -> TTerm f v -> Type (IxTerm f) -> Tc 'RuleCtx f v ()
check pos t tpe = do { tpe' <- infer pos t; tpe' `subtypeOf` tpe}

infer :: (Ord v, Ord f) => Pos -> TTerm f v -> Tc 'RuleCtx f v (Type (IxTerm f))
infer _   (TpVar _ v) = lookupEnv v >>= instantiateQ
infer pos (TpFun stout f ts) = do
  let stpe = MLTypes.curryType (DMInfer.typeOf `map` ts) stout
  fnTpe <- getCallingContext pos >>= declarationOf f stpe >>= instantiateQ
  (argTps,retTpe) <- assertJust (UnExpectedNumArgs f fnTpe (length ts)) (fnTpe `uncurryUpto` length ts)
  forM_ (zip3 [0..] ts argTps) $ \ (i, ai, ni) -> do
    (vs,ti) <- matrix ni
    withSkolemVars vs (check (pos `posAdd` i) ai ti)
  return retTpe
infer pos (TpApp _ t1 t2) = do
  funTpe <- infer (pos `posAdd` 0) t1
  case funTpe of
    TyArr argNTpe retTpe  -> do
      (vs,argTpe) <- matrix argNTpe
      withSkolemVars vs (check (pos `posAdd` 1) t2 argTpe)
      return retTpe
    _ -> error "SizeTypes.Infer: application with non-functional type"

-- TODO
simplify :: Eq f => [Constraint f] -> [Constraint f]
simplify = inlineSkolem . constifySkolem where 
  
  walk sks ds [] = (sks, ds)
  walk sks ds (c@(IxFun (IxSkolem uid) _ :>=: _) : cs) =
    case findDef uid [] sks of
     Just (c',sks') -> walk sks' (c:c':ds) cs
     Nothing -> walk (c:sks) ds cs
  walk sks ds (c:cs) = walk sks (c:ds) cs

  constifySkolem cs = [ l :>=: constify r | l :>=: r <- cs ] where
    lfuns = [ f | l :>=: _ <- cs, f <- indexSyms l ]
    constify IxZero = IxZero
    constify (IxSum ixs) = ixSum (constify `map` ixs)
    constify (IxSucc ix) = ixSucc (constify ix)
    constify (IxFun f@(IxSkolem _) ixs)
      | (f,length ixs) `notElem` lfuns = IxZero
    constify (IxFun f ixs) = IxFun f (constify `map` ixs)
    constify (IxVar v) = IxVar v

  inlineSkolem = uncurry inlineCs . walk [] []

  findDef _ _ [] = Nothing
  findDef uid sks (c@(IxFun (IxSkolem uid') _ :>=: _) : sks')
    | uid == uid' = Just (c,sks ++ sks')
  findDef uid sks (c:sks') = findDef uid (c:sks) sks'

  inlineCs [] ds = ds
  inlineCs (c:sks) ds = inlineCs (inlineC c `map` sks) (inlineC c `map` ds)
  inlineC c (l :>=: r) = inline c l :>=: inline c r
  inline _ IxZero = IxZero
  inline c (IxSucc ix) = IxSucc (inline c ix)
  inline c (IxSum ixs) = IxSum (inline c `map` ixs)
  inline c@(IxFun (IxSkolem uid) vs :>=: bdy) (IxFun (IxSkolem uid') as)
    | uid == uid' = s `o` bdy where
        s = substFromList (substLst vs as)
        substLst [] [] = []
        substLst (IxVar (FVar v):vs') (a:as') = (v,inline c a):substLst vs' as'
        substLst _ _ = error "SizeTypes.Infer: inlining not well-defined."
        
  inline c (IxFun f as) = IxFun f (inline c `map` as)
  inline _ (IxVar v) = IxVar v
  

----------------------------------------------------------------------
-- constraint solving
----------------------------------------------------------------------



data GSym f = GSum Int | GSym (IxSym f) deriving (Show, Eq, Ord)

type Interpretation f = GUBS.Interpretation (GSym f)
type Polynomial = GUBS.Polynomial IxVarId -- TODO IxVar
type CS f = GUBS.ConstraintSystem (GSym f) IxVar


toCS :: [Constraint f] -> CS f
toCS cs = [ gterm l GUBS.:>=: gterm r | l :>=: r <- cs ] where
  gterm IxZero = GUBS.Const 0
  gterm (IxSucc ix) = sumT [GUBS.Const 1, gterm ix]
  gterm (IxSum ixs) = sumT (gterm `map` ixs)
  gterm (IxVar v) = GUBS.Var v
  gterm (IxFun f ixs) = GUBS.Fun (GSym f) (gterm `map` ixs)
  sumT ts = GUBS.Fun (GSum (length ts)) ts 

interpretIx :: (Ord f, Eq c, Num c) => Interpretation f c -> IxTerm f -> Polynomial c
interpretIx _ IxZero = GUBS.constant 0
interpretIx _ (IxVar (BVar i)) = GUBS.variable i
interpretIx _ (IxVar (FVar i)) = GUBS.variable i
interpretIx inter (IxSum ixs) = sum (interpretIx inter `map` ixs)
interpretIx inter (IxSucc ix) = GUBS.constant 1 + interpretIx inter ix
interpretIx inter (IxFun f ixs) = GUBS.get' inter (GSym f) `GUBS.apply` (interpretIx inter `map` ixs)

interpretType :: (Ord f, Eq c, Num c) => Interpretation f c -> SizeType knd (IxTerm f) -> SizeType knd (Polynomial c)
interpretType _ (TyVar v) = TyVar v
interpretType inter (TyCon nm ix bs) = TyCon nm (interpretIx inter ix) (interpretType inter `map` bs)
interpretType inter (TyArr n t) = TyArr (interpretType inter n) (interpretType inter t)
interpretType inter (TyQ vs t) = TyQ vs (interpretType inter t)
  

-- TODO 
solveConstraints :: (MonadIO m, Ord f, PP.Pretty f) => [Constraint f] -> m (Maybe (Interpretation f Integer))
solveConstraints cs = GUBS.z3 (GUBS.solve initialInterpretation (toCS cs)) where
  initialInterpretation = GUBS.fromList [ (f, sum [GUBS.variable v | v <- take n GUBS.variables])
                                        | f@(GSum n) <- GSum 2 : concatMap (\ (l :>=: r) -> sums l ++ sums r) cs]
  sums IxZero = []
  sums (IxSucc ix) = sums ix
  sums (IxSum ixs) = (GSum (length ixs)) : sums `concatMap` ixs
  sums (IxVar _) = []
  sums (IxFun _ ixs) = sums `concatMap` ixs



withSimpleTypes :: (PP.Pretty v, Eq v, Ord f, PP.Pretty f) => Env v f -> ATerm f v -> SizeType knd ix -> Tc ctx f v (TTerm f v)
withSimpleTypes env t tpe = do
  ssig <- getStSignature
  either errOut return (DMInfer.check ssig senv t stpe) 
  where
    stpe = simpleTypeOf tpe
    senv = [ (v, simpleTypeOf n) | (v,n) <- Map.toList env ]
    errOut err = error $ "SizeTypes.checkRuleWith incompatible types: " ++ renderPretty err


generateConstraints :: (Ord f, Ord v, PP.Pretty f, PP.Pretty v) => Problem f v -> Tc 'GlobalCtx f v (Signature (f,CallingContext) (IxTerm f))
generateConstraints prob = do  
  forM_ (defs (startTerms prob)) $ \ f -> do
    (ins MLTypes.:~> out) <- getStDeclaration f
    freshDeclaration f emptyPos [] (Signature Map.empty) (MLTypes.curryType ins out)
  walk =<< (stQueue <$> get)
    where
      walk [] = stSig <$> get
      walk ((f,cs,declTpe,sig):queue) = do
        modify (\ st -> st { stQueue = queue } )
        forM_ [ (i, trl) | (i,trl) <- rulesEnum prob
                         , headSymbol (lhs (theRule trl)) == Just f ]
          $ \ (i, trl) -> do
          censor simplify $ do
            let rl = (theRule trl)
            (ixvs, env, lhsTpe) <- footprint (lhs rl) declTpe
            theRhs <- withSimpleTypes env (rhs rl) lhsTpe
            let ctx = TypingContext { tcEnv = env
                                    , tcFreeIxVars = ixvs
                                    , tcCallingContext = cs
                                    , tcSignature = sig
                                    , tcRule = rl
                                    , tcRuleNum = i }
            withTypingContext ctx (check emptyPos theRhs lhsTpe)
        walk =<< (stQueue <$> get)

----------------------------------------------------------------------
-- putting things together
----------------------------------------------------------------------

instance PP.Pretty v => PP.Pretty (GUBS.Monomial v) where
  pretty mono = pretty' (GUBS.toPowers mono) where
    pretty' [] = PP.char '1'
    pretty' ps = PP.hcat (PP.punctuate (PP.char '*') (map ppPower ps))
    ppPower (v,i) = PP.pretty v PP.<> if i == 1 then PP.empty else PP.char '^' PP.<> PP.int i      
  

instance (Eq c, Num c, PP.Pretty c, PP.Pretty v) => PP.Pretty (GUBS.Polynomial v c) where
  pretty poly = pretty' (GUBS.toMonos poly) where 
    pretty' [] = PP.char '0'
    pretty' ps = PP.hcat (PP.punctuate (PP.char '+') (map ppMono ps))
    ppMono (c,GUBS.toPowers -> []) = PP.pretty c
    ppMono (c,mono) = PP.pretty c PP.<> PP.char '*' PP.<> PP.pretty mono

instance (PP.Pretty f) => PP.Pretty (Signature (f,CallingContext) (Polynomial Integer)) where
  pretty (Signature m) = PP.vcat [PP.hang 2 $ PP.pretty f PP.<+> PP.text ":" PP.</> prettyType ppPoly n
                                 | ((f,_),n) <- Map.toList m]
    where 
      ppPoly p = PP.pretty (GUBS.rename BVar p)

instance (PP.Pretty f) => PP.Pretty (Signature (f,CallingContext) (IxTerm f)) where
  pretty (Signature m) = PP.vcat [PP.hang 2 $ PP.pretty f PP.<+> PP.text ":" PP.</> PP.pretty n
                                 | ((f,_),n) <- Map.toList m]

instance (PP.Pretty f) => PP.Pretty (Interpretation f Integer) where
  pretty inter = PP.vcat [PP.hang 2 $ PP.pretty f PP.<+> PP.text ":" PP.</> ppPoly n
                         | (GSym f,n) <- GUBS.toList inter]
    where 
      ppPoly p = PP.pretty (GUBS.rename BVar p)

inferSize :: (Show f, Ord f, Ord v, PP.Pretty f, PP.Pretty v) => Problem f v -> IO (Either (TypingError f v) (Signature (f,CallingContext) (Polynomial Integer)))
inferSize prob = runExceptT $ do
  (Signature sig,cs) <- runTc (generateConstraints prob) prob
  tracePretty (Signature sig) (return ())
  tracePretty cs (return ())
  int <- assertJust ConstraintsUnsolvable =<< solveConstraints cs
  tracePretty int (return ())
  return (Signature (interpretType int `fmap` sig))

