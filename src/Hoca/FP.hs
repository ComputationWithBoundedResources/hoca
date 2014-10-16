-- | A simple Functional Programming Language 

module Hoca.FP where

import qualified Hoca.PCF as PCF
import           Text.Parsec
import           Text.ParserCombinators.Parsec (CharParser)
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Control.Applicative ((<$>), (<*>))
import Control.Monad (void)


type Var = String
type Symbol = String
data Exp =
  Abs Var Exp
  | Var Var
  | Con Symbol [Exp]
  | App Exp Exp
  | Fix Exp
  | Cond Exp [(Symbol, [Var], Exp)]  
  | Let Var [Var] Exp Exp
  | LetRec Var [Var] Exp Exp
  deriving (Show)


prettyLet :: (PP.Pretty a1, PP.Pretty a) => String -> String -> [String] -> a -> a1 -> PP.Doc
prettyLet n v vs e1 e2 =
    PP.text n PP.<+> PP.hsep (map PP.text (v:vs)) PP.<+> PP.text "=" PP.<+> PP.pretty e1
    PP.<$> PP.text "in" PP.<+> PP.indent 0 (PP.pretty e2)

instance PP.Pretty Exp where
  pretty (Abs v e) = PP.parens (PP.text "fun" PP.<+> PP.text v PP.<+> PP.text "->" PP.<+> PP.pretty e)
  pretty (Var v) = PP.text v
  pretty (Con f as) =
    PP.pretty f PP.<> PP.encloseSep PP.lparen PP.rparen PP.comma [PP.pretty ai | ai <- as]
  pretty (App e1 e2) = PP.parens (PP.pretty e1 PP.<+> PP.pretty e2)
  pretty (Fix e) = PP.parens (PP.text "fix" PP.<+> PP.pretty e)
  pretty (Cond e cs) =
    PP.parens (PP.text "match" PP.<+> PP.pretty e PP.<+> PP.text "with"
               PP.<$> PP.vsep [ PP.text "|" PP.<> PP.pretty (Con g (map Var vs))
                                PP.<+> PP.text "->" PP.<+> PP.indent 2 (PP.pretty e')
                              | (g,vs,e') <- cs ])
  pretty (Let v vs e1 e2) = prettyLet "let" v vs e1 e2
  pretty (LetRec v vs e1 e2) = prettyLet "let rec" v vs e1 e2  
  
toPCF :: Exp -> Either String (PCF.Exp String)
toPCF = t []
  where
    t env (Abs v e) = PCF.Abs (Just v) <$> t env' e
      where env' = (v, 0::Int) : [(v',i+1) | (v',i) <- env]
    t env (Var v) = PCF.Var <$> maybe (Left ("variable " ++ show v ++ " not bound.")) Right (lookup v env)
    t env (Con g es) = PCF.Con (PCF.symbol g (length es)) <$> mapM (t env) es
    t env (App e1 e2) = PCF.App <$> t env e1 <*> t env e2
    t env (Fix e) = PCF.Fix <$> t env e
    t env (Cond e cs) =
      PCF.Cond Nothing <$> t env e <*> mapM tc cs
      where
        toBdy vs f = foldr Abs f vs
        tc (g, vs, f) = do
          f' <- t env (toBdy vs f)
          return (PCF.symbol g (length vs), f')   
    t env (Let v vs e1 e2) = t env (App (Abs v e2) (foldr Abs e1 vs))
    t env (LetRec v vs e1 e2) = t env (App (Abs v e2) (Fix (foldr Abs e1 (v:vs))))

-- * parsing

type Parser = CharParser ()

-- lexing
reservedWords :: [String]
reservedWords = words "fix let rec in = fun match with | ->"

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

term :: Parser Exp
term = (lambdaExp <?> "lambda expression")
       <|> (letExp <?> "let expression")
       <|> (fixExp <?> "fix expression")
       <|> (condExp <?> "match expression")               
       <|> foldl1 App <$> apps
  where
    apps = many1 ((try var <?> "variable")
                  <|> (constrExp <?> "constructor expression")
                  <|> (parens term <?> "parenthesised expression"))
           
    lambdaExp = do
      try (symbol "fun")
      vs <- many1 variable
      symbol "->"
      e <- term
      return (foldr Abs e vs)

    constructorWith arg = do
      g <- try constructor
      es <- try (parens (arg `sepBy` (symbol ","))) <|> return []
      return (g,es)
      
    constrExp = uncurry Con <$> constructorWith term

    letExp = do
      try (symbol "let")
      con <- try (symbol "rec" >> return LetRec) <|> return Let
      (v:vs) <- many1 variable
      symbol "="
      e1 <- term
      symbol "in"
      e2 <- term
      return (con v vs e1 e2)

    fixExp = do
      try (symbol "fix")
      e <- term
      return (Fix e)

    caseExp = do
      symbol "|"
      (g,vs) <- constructorWith variable
      symbol "->"
      e <- term
      return (g,vs,e)
      
    condExp  = do
      try (symbol "match")
      e <- term
      symbol "with"
      cs <- many1 caseExp
      return (Cond e cs)

    var = Var <$> variable

expFromString :: String -> String -> Either String Exp
expFromString source input = 
  case runParser p () source input of
   Left e -> Left (show e)
   Right r -> Right r
  where p = do {_ <- whiteSpace; t <- term; eof; return t }
