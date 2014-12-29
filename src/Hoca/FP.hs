-- | A simple Functional Programming Language 

module Hoca.FP where

import qualified Hoca.PCF as PCF
import           Text.Parsec
import           Text.ParserCombinators.Parsec (CharParser)
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Control.Applicative ((<$>), (<*>))
import Control.Monad.Reader (runReaderT, ask, local)
import Control.Monad.Error (throwError)
import Control.Monad (void)
import Data.Maybe (fromJust)
import qualified Data.Set as Set


type Var = String
type Symbol = String

data Pos = Pos {sn :: String, ln :: Int, cn :: Int}
           deriving (Show, Eq, Ord)

data Exp =
  Abs Pos Var Exp
  | Var Pos Var
  | Con Pos Symbol [Exp]
  | App Pos Exp Exp
  | Cond Pos Exp [(Symbol, [Var], Exp, Pos)]
  | Let Pos (Pos,Var,[Var],Exp) [(Pos,Var,[Var],Exp)] Exp
  | LetRec Pos (Pos,Var,[Var],Exp) [(Pos,Var,[Var],Exp)] Exp
  deriving (Show, Eq, Ord)

prettyLet :: String -> (Pos, String, [String], Exp) -> [(Pos, String, [String], Exp)] -> Exp -> PP.Doc
prettyLet n l ls e =
  PP.vsep [ PP.text m PP.<+> PP.hsep (map PP.text (v:vs)) PP.<+> PP.text "=" PP.<+> PP.pretty ei
          | (m,(_,v,vs,ei)) <- (n,l) : zip (repeat "and") ls]
  PP.<$> PP.text "in" PP.<+> PP.indent 0 (PP.pretty e)

prettyCon :: Symbol -> [PP.Doc] -> PP.Doc
prettyCon f ds = PP.pretty f PP.<> PP.encloseSep PP.lparen PP.rparen PP.comma ds

instance PP.Pretty Exp where
  pretty (Abs _ v e) = PP.parens (PP.text "fun" PP.<+> PP.text v PP.<+> PP.text "->" PP.<+> PP.pretty e)
  pretty (Var _ v) = PP.text v
  pretty (Con _ f as) = prettyCon f (map PP.pretty as)
    
  pretty (App _ e1 e2) = PP.parens (PP.pretty e1 PP.<+> PP.pretty e2)
  pretty (Cond _ e cs) =
    PP.parens (PP.text "match" PP.<+> PP.pretty e PP.<+> PP.text "with"
               PP.<$> PP.vsep [ PP.text "|" PP.<+> prettyCon g (map PP.text vs)
                                PP.<+> PP.text "->" PP.<+> PP.indent 2 (PP.pretty e')
                              | (g,vs,e',_) <- cs ])
  pretty (Let _ l ls e) = prettyLet "let" l ls e
  pretty (LetRec _ l ls e) = prettyLet "let rec" l ls e

sourcePos :: Exp -> Pos
sourcePos (Abs l _ _) = l
sourcePos (Var l _) = l
sourcePos (Con l _ _) = l
sourcePos (App l  _ _) = l
sourcePos (Cond l _ _) = l
sourcePos (Let l _ _ _) = l
sourcePos (LetRec l _ _ _) = l


data ProgramPoint =
  LetBdy Symbol [Symbol] Exp
  | LetRecBdy Symbol [Symbol] Exp  
  | LetIn Exp
  | LambdaBdy Exp
  | LApp Exp
  | RApp Exp
  | CaseGuard Exp
  | CaseBdy Symbol [Symbol] Exp
  | ConstructorArg Int Exp
    deriving (Show, Eq, Ord)
             
type Context = [ProgramPoint]

freeVars :: Exp -> Set.Set Var
freeVars (Abs _ v e) = Set.delete v (freeVars e)
freeVars (Var _ v) = Set.insert v Set.empty
freeVars (App _ e1 e2) = freeVars e1 `Set.union` freeVars e2
freeVars (Con _ _ es) = Set.unions [ freeVars e | e <- es]
freeVars (Cond _ g cs) =
  Set.unions (freeVars g
              : [ freeVars e Set.\\ Set.fromList vs
                | (_,vs,e, _) <- cs ])
freeVars (Let _ d ds e) =
  Set.unions (freeVars e Set.\\ fs : [ freeVars ef Set.\\ Set.fromList vs | (_,_,vs,ef) <- d:ds ])
  where
    fs = Set.fromList [f | (_,f,_,_) <- d:ds]
freeVars (LetRec _ d ds e) =
  Set.unions (freeVars e : [ freeVars ef Set.\\ Set.fromList vs | (_,_,vs,ef) <- d:ds ])
  Set.\\ fs
  where
    fs = Set.fromList [f | (_,f,_,_) <- d:ds]

toPCF :: Exp -> Either String (PCF.Exp Context)
toPCF expr = runReaderT (pcf (close expr)) ([],[])
  where

    close e = foldr (Abs (Pos "toPCF" 0 0)) e (Set.toList (freeVars e))
      
    environment = fst <$> ask
    context = snd <$> ask

    withVar v = local (\ (env,ctx) -> (newEnv env, ctx)) where
      newEnv env = (v, 0::Int) : [(v',i+1) | (v',i) <- env]
    withContext ctx = local (\ (env,ctx') -> (env, ctx ++ ctx'))

    lambda v m = PCF.Abs (Just v) <$> context <*> withVar v m

    letExp e v vs f = letBdy [] vs where
      letBdy zs []       = withContext [LetBdy v zs e] (pcf f)
      letBdy zs (v':vs') = withContext [LetBdy v zs e] (lambda v' (letBdy (v':zs) vs'))

    pcf e@(Abs _ v f) = lambda v (withContext [LambdaBdy e] (pcf f))

    pcf (Var pos v) = do
      mv <- lookup v <$> environment
      case mv of
       Just i -> PCF.Var <$> context <*> return i
       Nothing -> throwError ("Variable " ++ show v ++ " at line " ++ show (ln pos)
                              ++ ", column " ++ show (cn pos) ++ " not bound.")
      
    pcf e@(Con _ g es) =
      PCF.Con <$> context <*> return g'
       <*> sequence [withContext [ConstructorArg i e] (pcf ei)
                    | (i,ei) <- zip [1..] es]
      where g' = PCF.symbol g (length es)
            
    pcf e@(App _ e1 e2) =
      PCF.App <$> context
       <*> withContext [LApp e] (pcf e1)
       <*> withContext [RApp e] (pcf e2)
       
    pcf e@(Cond _ gexp cs) = 
      PCF.Cond <$> context
       <*> withContext [CaseGuard e] (pcf gexp)
       <*> sequence [ (PCF.symbol g (length vs),) <$> caseBdy g c [] vs
                    | (g, vs, c, _) <- cs ]
      where
        caseBdy g c zs []      = withContext [CaseBdy g zs e] (pcf c)
        caseBdy g c zs (v:vs') = withContext [CaseBdy g zs e] (lambda v (caseBdy g c (v:zs) vs'))
        
    pcf e@(Let _ d1 ds e2) = do
      e2' <- foldr lambda (withContext [LetIn e] (pcf e2)) fs -- \ f1..fn -> [e2]
      es <- sequence [ letExp e fi vsi ei | (_,fi,vsi,ei) <- d1:ds ]
      return (fromJust (PCF.applyL e2' es))
      where fs = [ f | (_,f,_,_)  <- d1 : ds]

    pcf e@(LetRec _ d1 ds e2) = do
      e2' <- foldr lambda (withContext [LetIn e] (pcf e2)) fs -- \ f1..fn -> [e2]
      es <- sequence [ letRecExp fi vsi ei | (_,fi,vsi,ei) <- d1 : ds] -- [.. \ f1..fn v1..vm -> [ei] ..]
      return (fromJust (PCF.applyL e2' [ PCF.Fix i es | i <- [0..length ds] ]))
      where
        fs = [ f | (_,f,_,_)  <- d1 : ds]
        letRecExp f vs b = letRecBdy [] fs where
          letRecBdy zs []       = withContext [LetRecBdy f zs e] (letExp e f vs b)
          letRecBdy zs (fi:fs') = withContext [LetRecBdy f zs e] (lambda fi (letRecBdy (fi:zs) fs'))
      

-- * parsing

type Parser = CharParser ()

-- lexing
reservedWords :: [String]
reservedWords = words "let rec in = fun match with | -> and ;;"

whiteSpace :: Parser String
whiteSpace = many ((space <|> tab <|> newline) <?> "whitespace")

whiteSpace1 :: Parser String
whiteSpace1 = many1 ((space <|> tab <|> newline) <?> "whitespace")

comment :: Parser String
comment = (string "(*" >> manyTill anyChar (try (string "*)"))) <?> "comment"

lexeme :: Parser a -> Parser a
lexeme p = do { x <- p; _ <- many (try comment <|> whiteSpace1); return x }

symbol :: String -> Parser ()
symbol name = void (lexeme (string name) <?> "keyword '" ++ name ++ "'")

identifier :: Parser String -> Parser String
identifier p = do
  s <- lexeme p
  if s `elem` reservedWords
   then unexpected ("reserved word " ++ show s)
   else return s

ident' :: Parser String
ident' = many (try alphaNum <|> oneOf "'_/#?")

variable :: Parser String
variable = identifier ((:) <$> lower <*> ident') <?> "variable"

constructor :: Parser String
constructor = identifier ((:) <$> (try upper <|> digit) <*> ident') <?> "constructor"

parens :: Parser a -> Parser a
parens = between (char '(' >> notFollowedBy (char '*')) (lexeme (char ')'))

-- parsing

posP :: Parser Pos
posP = do
  p <- getPosition
  return Pos { sn = sourceName p, ln = sourceLine p, cn = sourceColumn p}

withPos :: Parser a -> Parser (Pos,a)
withPos p = (,) <$> posP <*> p
  
term :: Parser Exp
term = (lambdaExp <?> "lambda expression")
       <|> (letExp <?> "let expression")
       <|> (condExp <?> "match expression")               
       <|> (appExp <?> "application")
  where
    
    appExp = do
      (_,e):es <-
        many1 ((try (withPos var) <?> "variable")
               <|> (withPos constrExp <?> "constructor expression")
               <|> (parens (withPos term) <?> "parenthesised expression"))
      return (foldl (\ f1 (p,f2) -> App p f1 f2) e es)
           
    lambdaExp = do
      pos <- posP
      try (symbol "fun")
      vs <- many1 variable
      symbol "->"
      e <- term
      return (foldr (Abs pos) e vs)

    constructorWith arg = do
      g <- try constructor
      es <- try (parens (arg `sepBy` symbol ",")) <|> return []
      return (g,es)
      
    constrExp = do
      pos <- posP
      uncurry (Con pos) <$> constructorWith term

    letExp = do
      pos <- posP
      try (symbol "let")
      con <- try (symbol "rec" >> return LetRec) <|> return Let
      (l:ls) <- letBinding `sepBy1` symbol "and"
      try (symbol "in") <|> symbol ";;" -- hack
      e <- term
      return (con pos l ls e)
      where
        letBinding = do
          pos <- posP
          (v:vs) <- many1 variable
          symbol "="
          e <- term
          return (pos, v, vs, e)
          
    caseExp = do
      pos <- posP
      symbol "|"
      (g,vs) <- constructorWith variable
      symbol "->"
      e <- term
      return (g,vs,e,pos)
      
    condExp  = do
      pos <- posP
      try (symbol "match")
      e <- term
      symbol "with"
      cs <- many1 caseExp
      return (Cond pos e cs)

    var = Var <$> posP <*> variable

expFromString :: String -> String -> Either String Exp
expFromString source input = 
  case runParser p () source input of
   Left e -> Left (show e)
   Right r -> Right r
  where p = do {_ <- many (try comment <|> whiteSpace1); t <- term; eof; return t }
