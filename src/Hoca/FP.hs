-- | A simple Functional Programming Language 

module Hoca.FP where

import qualified Hoca.PCF as PCF
import           Text.Parsec
import           Text.ParserCombinators.Parsec (CharParser)
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Control.Applicative ((<$>), (<*>))
import Control.Monad (void,foldM)


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
  deriving (Show)

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
  LetBdy String [String] Exp
  | LetRecBdy String [String] Exp  
  | LetArg String String Exp
  | LetBoundVar String Exp            
  | LetIn Exp
  | LambdaBdy Exp
  | LambdaVar String Exp
  | LApp Exp
  | RApp Exp
  | CaseGuard Exp
  | CaseBdy Symbol Exp
  | CaseVar String Symbol Exp    
  | ConstructorArg Int Exp
    deriving (Show)
             
type Context = [ProgramPoint]
           
toPCF :: Exp -> Either String (PCF.Exp Context)
toPCF = t [] []
  where
    
    pushEnv env v = (v, 0::Int) : [(v',i+1) | (v',i) <- env]

    toAbs mkBdyCtx mkVCtx = toAbs' [] where
      toAbs' zs ctx env [] b = t (mkBdyCtx zs ++ ctx) env b
      toAbs' zs ctx env (v:vs) b =
        PCF.Abs (mkVCtx v ++ ctx) bdyCtx
        <$> toAbs' (v : zs) bdyCtx (pushEnv env v) vs b
        where bdyCtx = mkBdyCtx zs ++ ctx

    t ctx env (Var pos v) = do
      i <- case lookup v env of
            Just i -> Right i
            Nothing -> Left ("Variable " ++ show v ++ " at line " ++ show (ln pos)
                             ++ ", column " ++ show (cn pos) ++ " not bound.")
      return (PCF.Var ctx i)

    t ctx env e@(Abs _ v f) =
      toAbs (const [LambdaBdy e]) (const [LambdaVar v e]) ctx env [v] f
          
    t ctx env e@(Con _ g es) =
      PCF.Con ctx (PCF.symbol g (length es))
       <$> mapM ( \ (i,ei) -> t (ConstructorArg i e: ctx) env ei) (zip [1..] es)
      
    t ctx env e@(App _ e1 e2) =
      PCF.App ctx <$> t (LApp e : ctx) env e1 <*> t (RApp e : ctx) env e2
    t ctx env e@(Cond _ gexp cs) = 
      PCF.Cond ctx <$> t (CaseGuard e:ctx) env gexp
                   <*> mapM tc cs
      where
        tc (g, vs, c, _) = do
          c' <- toAbs (const [CaseBdy g e]) (\ v -> [CaseVar v g e]) ctx env vs c 
          return (PCF.symbol g (length vs), c')

    t ctx env e@(Let _ d1 d2s e2) = tLet d1 d2s where
      tLet (_,v,vs,e1) [] =
        PCF.App ctx
          <$> toAbs (const [LetIn e]) (\v' -> [LetBoundVar v' e]) ctx env [v] e2
          <*> toAbs (\vs' -> [LetBdy v vs' e]) (\ v' -> [LetArg v v' e]) ctx env vs e1
      tLet (_,v,vs,e1) (d:ds) =
        PCF.App ctx
          <$> tLet d ds
          <*> toAbs (\vs' -> [LetBdy v vs' e]) (\ v' -> [LetArg v v' e]) ctx env vs e1

    t ctx env e@(LetRec _ d1 d2s e2) = do
      e2' <- toAbs (const [LetIn e]) (\ v' -> [LetBoundVar v' e]) ctx env fs e2
      e1s <- sequence [toAbs (\ vs' -> [LetRecBdy f vs' e]) (\ v' -> [LetArg f v' e]) ctx env (fs++vsi) ei
                      | (_,f,vsi,ei) <- ds]
      return (foldl (\ e' i -> PCF.App ctx e' (PCF.Fix i e1s)) e2' [0..length ds - 1])
        where 
          ds = d1 : d2s
          fs = [ f | (_,f,_,_)  <- ds]
    -- -- letrec v vs = e1 in e2 == (\v . e2) (fix (\ v vs . e1))
    -- t ctx env e@(LetRec _ v vs e1 e2) =
    --   PCF.App ctx
    --    <$> toAbs (const (LetIn v e)) (\ v' -> LetArg v v' e) ctx env [v] e2 
    --    <*> (PCF.Fix <$> toAbs (\ vs' -> LetRecBdy v vs' e) (\ v' -> LetArg v v' e) ctx env (v:vs) e1)
      

-- * parsing

type Parser = CharParser ()

-- lexing
reservedWords :: [String]
reservedWords = words "let rec in = fun match with | -> and"

whiteSpace :: Parser String
whiteSpace = many ((space <|> tab <|> newline) <?> "whitespace")

lexeme :: Parser a -> Parser a
lexeme p = do { x <- p; _ <- whiteSpace; return x }

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
parens = between (symbol "(") (symbol ")")

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
      symbol "in"
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
  where p = do {_ <- whiteSpace; t <- term; eof; return t }
