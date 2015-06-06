-- | 

module Hoca.PCF.Desugar (
  desugar
  , desugarExpression
  ) where

import qualified Hoca.PCF.Core as PCF
import           Hoca.PCF.Sugar.Types
import qualified Hoca.Data.MLTypes as Tpe
import           Control.Monad.Reader (ReaderT, MonadReader, runReaderT, ask, local)
import           Control.Monad.Except (MonadError, throwError)
import           Control.Arrow (first, second)
import           Data.Maybe (isNothing)
import qualified Data.Map as Map

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
run = flip runReaderT ([],mempty) . runDesugarM

environment :: DesugarM [(Variable, Int)]
environment = fst <$> ask

context :: DesugarM Context
context = snd <$> ask

withVar :: Variable -> DesugarM a -> DesugarM a
withVar v = local (first newEnv) where
  newEnv env = (v, 0::Int) : [(v',i+1) | (v',i) <- env]

withEmptyContext :: DesugarM a -> DesugarM a
withEmptyContext = local (second (const mempty))

withContext :: [ProgramPoint] -> DesugarM a -> DesugarM a
withContext ctx = local (second (Context ctx `mappend`))


pcfSymbol :: Symbol -> Int -> PCF.Symbol
pcfSymbol (Symbol n) = PCF.symbol n


lambda :: Variable -> DesugarM (PCF.Exp Context) -> DesugarM (PCF.Exp Context)
lambda v@(Variable n) m = PCF.Abs <$> context <*> return (Just n) <*> withVar v m

anonymous :: DesugarM (PCF.Exp Context) -> DesugarM (PCF.Exp Context)
anonymous m = PCF.Abs <$> context <*> return Nothing <*> withVar (Variable "_") m    


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
  return (foldl (PCF.App ctx) f' [ PCF.Fix ctx i es | i <- [0..length ds-1] ])
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
                          
desugarExp (Err _) = PCF.Bot <$> context
  
desugarExp (Con _ g es) =
  PCF.Con <$> context <*> return g'
   <*> sequence [withContext [ConstructorArg (i + 1) (es!!i)] (desugarExp ei)
                | (i,ei) <- zip [0..] es]
  where g' = pcfSymbol g (length es)
desugarExp (App _ e1 e2) =
  PCF.App <$> context 
          <*> withContext [Lapp e1] (desugarExp e1) 
          <*> withContext [Rapp e2] (desugarExp e2)
desugarExp e@(Lazy _ f) =
  anonymous (withContext [LazyBdy e] (desugarExp f))
desugarExp e@(Force _ f) = 
  PCF.App <$> context
   <*> withContext [ForceBdy e] (desugarExp f)
   <*> return (PCF.Bot mempty)
desugarExp (Cond _ gexp cs) = 
  PCF.Cond <$> context
   <*> withContext [CaseGuard gexp] (desugarExp gexp)
   <*> sequence [ (pcfSymbol g (length vs),) <$> caseBdy g c [] vs
                | (g, vs, c, _) <- cs ]
  where
    caseBdy g c zs []      = withContext [CaseBdy g zs c] (desugarExp c)
    caseBdy g c zs (v:vs') = withContext [CaseBdy g zs c] (lambda v (caseBdy g c (v:zs) vs'))
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
desugarExpression e = run (desugarExp e)

signatureFromPrologue :: [TypeDecl] -> Either String (Tpe.Signature PCF.Symbol)
signatureFromPrologue ds = Tpe.signatureFromList <$> concat <$> mapM fromDecl ds where
  fromDecl d = do 
    tret <- fromSType (TyCon (typeName d) (TyVar `map` typeVars d))
    fromCase tret `mapM` typeList d 
    
      where       
        TypeName m = typeName d
        dict = zip (typeVars d) [0..]

        fromCase tret (Symbol f, ts) = do 
          targs <- fromSType `mapM` ts
          return (PCF.symbol f (length targs) Tpe.::: targs Tpe.:~> tret)        

        fromSType (TyVar v@(TypeVar n)) = 
          case lookup v dict of 
           Just i -> return (Tpe.TyVar i)
           Nothing -> throwError ("type variable '" ++ n
                                  ++ "' not bound in declaration of type '" 
                                  ++ m ++ "'.") 
        fromSType (TyCon (TypeName n) ts) = Tpe.TyCon n <$> mapM fromSType ts
        fromSType (t1 :~> t2) = (Tpe.:->) <$> fromSType t1 <*> fromSType t2
      
desugar :: Maybe String -> Program -> Either String (PCF.Program Context)
desugar mname prog = do
  sig <- signatureFromPrologue (prologue prog)
  e <- run (desugarDecls ds =<< getMainCall (concatMap defs ds)) 
  return PCF.Program { PCF.signature = sig , PCF.expression = e}
    where
      ds = functions prog
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

    


