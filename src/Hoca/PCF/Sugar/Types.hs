-- | 

module Hoca.PCF.Sugar.Types where

import qualified Data.Set as Set
import Data.Monoid (Monoid)

-- | constructors
newtype Symbol = Symbol String deriving (Eq, Ord, Show) 

-- | variables
newtype Variable = Variable String deriving (Ord, Eq, Show)

----------------------------------------------------------------------
-- type expressions / declarations
----------------------------------------------------------------------

-- | type variables  
newtype TypeVar = TypeVar String deriving (Eq, Ord, Show) 

-- | type names
newtype TypeName = TypeName String deriving (Eq, Ord, Show) 

data Type = TyVar TypeVar -- ^ variable
          | TyCon TypeName [Type] -- ^ composite type
          | Type :~> Type -- ^ arrow type

-- | recursive sum types
data TypeDecl = TypeDecl { typeName :: TypeName -- ^ name
                         , typeVars :: [TypeVar] -- ^ free variables
                         , typeList :: [(Symbol,[Type])] -- ^ cases
                         }

----------------------------------------------------------------------
-- expressions
----------------------------------------------------------------------

-- | position in a source
data Pos = Pos {sn :: String -- ^ source name
               , ln :: Int -- ^ line number
               , cn :: Int -- ^ column number
               }
         deriving (Show, Eq, Ord)

-- | expressions
data Exp =
  Abs Pos Variable Exp -- ^ abstraction
  | Var Pos Variable -- ^ variable
  | Err Pos -- ^ used to handle error function  
  | Con Pos Symbol [Exp] -- ^ constructor
  | App Pos Exp Exp -- ^ application
  | Lazy Pos Exp -- ^ lazy keyword
  | Force Pos Exp -- ^ force keyword    
  | Cond Pos Exp [(Symbol, [Variable], Exp, Pos)] -- ^ match statements
  | Let Pos [(Pos,Variable,[Variable],Exp)] Exp -- ^ non-recursive lets
  | LetRec Pos [(Pos,Variable,[Variable],Exp)] Exp -- ^ recursive lets
  deriving (Show, Eq, Ord)

-- | set of free variables
freeVars :: Exp -> Set.Set Variable
freeVars (Abs _ v e) = Set.delete v (freeVars e)
freeVars (Var _ v) = Set.insert v Set.empty
freeVars (Lazy _ e) = freeVars e
freeVars (Err _) = Set.empty
freeVars (Force _ e) = freeVars e
freeVars (App _ e1 e2) = freeVars e1 `Set.union` freeVars e2
freeVars (Con _ _ es) = Set.unions [ freeVars e | e <- es ]
freeVars (Cond _ g cs) =
  Set.unions (freeVars g
              : [ freeVars e Set.\\ Set.fromList vs
                | (_,vs,e, _) <- cs ])
freeVars (Let _ ds e) =
  Set.unions (freeVars e Set.\\ fs : [ freeVars ef Set.\\ Set.fromList vs | (_,_,vs,ef) <- ds ])
  where
    fs = Set.fromList [f | (_,f,_,_) <- ds]
freeVars (LetRec _ ds e) =
  Set.unions (freeVars e : [ freeVars ef Set.\\ Set.fromList vs | (_,_,vs,ef) <- ds ])
  Set.\\ fs
  where
    fs = Set.fromList [f | (_,f,_,_) <- ds]

-- | source position of overall expression
sourcePos :: Exp -> Pos
sourcePos (Err l) = l
sourcePos (Abs l _ _) = l
sourcePos (Lazy l _) = l
sourcePos (Force l _) = l
sourcePos (Var l _) = l
sourcePos (Con l _ _) = l
sourcePos (App l  _ _) = l
sourcePos (Cond l _ _) = l
sourcePos (Let l _ _) = l
sourcePos (LetRec l _ _) = l

-- | Contextual informations for an expression

data ProgramPoint =
  LetBdy Variable [Variable] Exp
  | LetRecBdy Variable [Variable] Exp  
  | LazyBdy Exp
  | ForceBdy Exp
  | CaseGuard Exp
  | CaseBdy Symbol [Variable] Exp
  | ConstructorArg Int Exp
  | Lapp Exp
  | Rapp Exp  
    deriving (Show, Eq, Ord)
             
newtype Context = Context [ProgramPoint] deriving (Eq, Ord, Monoid)


----------------------------------------------------------------------
-- programs
----------------------------------------------------------------------

-- | type for function declaration. The quadruple @(p,f,xs,e)@ indicates
-- a declaration @let [rec] f xs = e@ at source position @p@ 
data FunDecl =
  FunDeclLet Pos [(Pos,Variable,[Variable],Exp)] -- ^ non-recursive function declaration
  | FunDeclRec Pos [(Pos,Variable,[Variable],Exp)] -- ^ recursive function declaration

data Program = Program { prologue :: [TypeDecl]
                       , functions :: [FunDecl]}

