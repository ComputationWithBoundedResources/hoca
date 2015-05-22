-- | 

module Hoca.PCF.Desugar (
  desugar
  , desugarExpression
  ) where

import qualified Hoca.PCF.Core as PCF
import           Hoca.PCF.Sugar.Types

import           Control.Monad.Reader (ReaderT, MonadReader, runReaderT, ask, local)
import           Control.Monad.Error (MonadError, throwError)
import           Control.Arrow (first, second)
import           Data.Maybe (fromJust,isNothing)
import           Control.Applicative ((<$>), Applicative(..))

-- desugaring monad
newtype DesugarM a =
  DesugarM { runDesugarM :: ReaderT ([(Variable, Int)], Context) (Either String) a }
  deriving (
    Monad
    , Functor
    , Applicative
    , MonadReader (
      [(Variable, Int)] -- mapping to De-Bruin indices
      , Context -- current context of expression
      )
    , MonadError String)

run :: DesugarM a -> Either String a
run = flip runReaderT ([],[]) . runDesugarM

environment :: DesugarM [(Variable, Int)]
environment = fst <$> ask

context :: DesugarM Context
context = snd <$> ask

withVar :: Variable -> DesugarM a -> DesugarM a
withVar v = local (first newEnv) where
  newEnv env = (v, 0::Int) : [(v',i+1) | (v',i) <- env]

withEmptyContext :: DesugarM a -> DesugarM a
withEmptyContext = local (second (const []))

withContext :: Context -> DesugarM a -> DesugarM a
withContext ctx = local (second (ctx ++))


pcfSymbol :: Symbol -> Int -> PCF.Symbol
pcfSymbol (Symbol n) = PCF.symbol n


lambda :: Variable -> DesugarM (PCF.Exp Context) -> DesugarM (PCF.Exp Context)
lambda v@(Variable n) m = PCF.Abs (Just n) <$> context <*> withVar v m

anonymous :: DesugarM (PCF.Exp Context) -> DesugarM (PCF.Exp Context)
anonymous m = PCF.Abs Nothing <$> context <*> withVar (Variable "_") m    


letToLambda :: Variable -> [Variable] -> Exp -> DesugarM (PCF.Exp Context)
letToLambda v vs f = letBdy [] vs where
  letBdy zs []       = withContext [LetBdy v zs f] (desugarExp f)
  letBdy zs (v':vs') = withContext [LetBdy v zs f] (lambda v' (letBdy (v':zs) vs'))

desugarLet :: [(Pos, Variable, [Variable], Exp)] -> DesugarM (PCF.Exp Context) -> DesugarM (PCF.Exp Context)
desugarLet ds mf = do
  f' <- foldr lambda mf fs -- \ f1..fn -> [f]
  es <- sequence [ letToLambda fi vsi ei | (_,fi,vsi,ei) <- ds ]
  ctx <- context
  return (foldl (PCF.App ctx) f' es)
    where fs = [ fn | (_,fn,_,_)  <- ds]

desugarLetRec :: [(Pos, Variable, [Variable], Exp)] -> DesugarM (PCF.Exp Context) -> DesugarM (PCF.Exp Context)
desugarLetRec ds mf = do
  f' <- foldr lambda mf fs -- \ f1..fn -> [f]
  es <- sequence [ letRecExp fi vsi ei | (_,fi,vsi,ei) <- ds] -- [.. \ f1..fn v1..vm -> [ei] ..]
  ctx <- context
  return (foldl (PCF.App ctx) f' [ PCF.Fix i ctx es | i <- [0..length ds-1] ])
    where
      fs = [ fn | (_,fn,_,_)  <- ds]
      letRecExp f vs b = letRecBdy [] fs where
        letRecBdy zs []       = withContext [LetRecBdy f zs b] (letToLambda f vs b)
        letRecBdy zs (fi:fs') = withContext [LetRecBdy f zs b] (lambda fi (letRecBdy (fi:zs) fs'))
  
desugarExp :: Exp -> DesugarM (PCF.Exp Context)
desugarExp (Abs _ v f) = lambda v (desugarExp f)
desugarExp (Var pos v@(Variable n)) = do
  mv <- lookup v <$> environment
  case mv of
   Just i -> PCF.Var <$> context <*> return i
   Nothing -> throwError ("Variable " ++ show n ++ " at line " ++ show (ln pos)
                          ++ ", column " ++ show (cn pos) ++ " not bound.")
desugarExp e@(Con _ g es) =
  PCF.Con <$> context <*> return g'
   <*> sequence [withContext [ConstructorArg i e] (desugarExp ei)
                | (i,ei) <- zip [1..] es]
  where g' = pcfSymbol g (length es)
desugarExp (App _ e1 e2) =
  PCF.App <$> context <*> (desugarExp e1) <*> (desugarExp e2)
desugarExp e@(Lazy _ f) =
  anonymous (withContext [LazyBdy e] (desugarExp f))
desugarExp e@(Force _ f) = 
  PCF.App <$> context
   <*> withContext [ForceBdy e] (desugarExp f)
   <*> return (PCF.Bot [])
desugarExp e@(Cond _ gexp cs) = 
  PCF.Cond <$> context
   <*> withContext [CaseGuard e] (desugarExp gexp)
   <*> sequence [ (pcfSymbol g (length vs),) <$> caseBdy g c [] vs
                | (g, vs, c, _) <- cs ]
  where
    caseBdy g c zs []      = withContext [CaseBdy g zs e] (desugarExp c)
    caseBdy g c zs (v:vs') = withContext [CaseBdy g zs e] (lambda v (caseBdy g c (v:zs) vs'))
desugarExp (Let _ ds f) = desugarLet ds (desugarExp f)
desugarExp (LetRec _ ds f) = desugarLetRec ds (desugarExp f)
 
desugarDecl :: FunDecl -> DesugarM (PCF.Exp Context) -> DesugarM (PCF.Exp Context)
desugarDecl (FunDeclLet _ ds) f = withEmptyContext (desugarLet ds f)
desugarDecl (FunDeclRec _ ds) f = withEmptyContext (desugarLetRec ds f)

desugarDecls :: [FunDecl] -> (Variable,[Variable]) -> DesugarM (PCF.Exp Context)
desugarDecls ds (f,vs) = foldr lambda (foldr desugarDecl (desugarExp main) ds) vs where
  main = foldl (App p) (Var p f) [Var p v | v <- vs ]
  p = Pos "" 0 0

desugarExpression :: Exp -> Either String (PCF.Exp Context)
desugarExpression exp = run (desugarExp exp)

desugar :: Maybe String -> Program -> Either String (PCF.Exp Context)
desugar mname prog = run (desugarDecls ds =<< getMainCall (concatMap defs ds)) where
  ds = fundecs prog
  defs (FunDeclLet _ ds') = ds'
  defs (FunDeclRec _ ds') = ds'  
  getMainCall [] =
    case mname of
     Just name -> throwError ("program contains no function named '" ++ name ++ "'")
     _ -> throwError "program contains no function definition"
  getMainCall [(_,f,vs,_)]
    | isNothing mname = return (f,vs)
  getMainCall ((_,f@(Variable name),vs,_):ds')
    | Just name == mname = return (f,vs)
    | otherwise = getMainCall ds'
    
--    

    


