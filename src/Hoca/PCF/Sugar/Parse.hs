module Hoca.PCF.Sugar.Parse
       (
         programFromString
       , expressionFromString
       ) where

import Control.Monad (void)
import Data.Either (partitionEithers)
import Hoca.PCF.Sugar.Types
import Text.Parsec
import Text.ParserCombinators.Parsec (CharParser)

-- | parser for programs with syntactic suggar. Stores
-- already parsed types, together with the number of free variables.
type Parser = CharParser [(TypeName,Int)]

----------------------------------------------------------------------
-- lexing
----------------------------------------------------------------------

reservedWords :: [String]
reservedWords = words "type let rec in = of fun match with | -> and ;; lazy force error"

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

variable :: Parser Variable
variable = Variable <$> identifier ((:) <$> lower <*> ident') <?> "variable"

constructor :: Parser Symbol
constructor = Symbol <$> identifier ((:) <$> (try upper <|> digit) <*> ident') <?> "constructor"

parens :: Parser a -> Parser a
parens = between (char '(' >> notFollowedBy (char '*')) (lexeme (char ')'))


----------------------------------------------------------------------
-- parsers
----------------------------------------------------------------------
posP :: Parser Pos
posP = do
  p <- getPosition
  return Pos { sn = sourceName p, ln = sourceLine p, cn = sourceColumn p}

withPos :: Parser a -> Parser (Pos,a)
withPos p = (,) <$> posP <*> p
  
expP :: Parser Exp
expP = (lambdaExp <?> "lambda expression")
       <|> (lazyExp <?> "lazy expression")
       <|> (forceExp <?> "forced expression")       
       <|> (letExp <?> "let expression")
       <|> (condExp <?> "match expression")               
       <|> (appExp <?> "application")
  where
    
    appExp = do
      (_,e):es <-
        many1 ((try (withPos var) <?> "variable")
               <|> (withPos constrExp <?> "constructor expression")
               <|> (withPos errorExp <?> "error expression")
               <|> (parens (withPos expP) <?> "parenthesised expression"))
      return (foldl (\ f1 (p,f2) -> App p f1 f2) e es)

    errorExp = do 
     pos <- posP
     symbol "error"
     return (Err pos)
     
    lambdaExp = do
      pos <- posP
      try (symbol "fun")
      vs <- many1 variable
      symbol "->"
      e <- expP
      return (foldr (Abs pos) e vs)

    lazyExp = do
      pos <- posP
      try (symbol "lazy")
      e <- expP
      return (Lazy pos e)

    forceExp = do
      pos <- posP
      try (symbol "force")
      e <- expP
      return (Force pos e)
      
    constructorWith arg = do
      g <- try constructor
      es <- try (parens (arg `sepBy` symbol ",")) <|> return []
      return (g,es)
      
    constrExp = do
      pos <- posP
      uncurry (Con pos) <$> constructorWith expP

    letExp = do
      pos <- posP
      try (symbol "let")
      con <- try (symbol "rec" >> return LetRec) <|> return Let
      ls <- letBinding `sepBy1` symbol "and"
      try (symbol "in")
      e <- expP
      return (con pos ls e)
      where
        letBinding = do
          pos <- posP
          (v:vs) <- many1 variable
          symbol "="
          e <- expP
          return (pos, v, vs, e)
          
    caseExp = do
      pos <- posP
      symbol "|"
      (g,vs) <- constructorWith variable
      symbol "->"
      e <- expP
      return (g,vs,e,pos)
      
    condExp  = do
      pos <- posP
      try (symbol "match")
      e <- expP
      symbol "with"
      cs <- many1 caseExp
      return (Cond pos e cs)

    var = Var <$> posP <*> variable


typeVarP :: Parser TypeVar
typeVarP = char '\'' >> (tvar <$> identifier ((:) <$> lower <*> ident')) <?> "type variable"
  where tvar = TypeVar

typeP :: Parser Type
typeP = tyFun <?> "type"
  where
    tyVar = TyVar <$> typeVarP
    tyFun = foldr1 (:~>) <$> tyNFun `sepBy1` symbol "->"
    tyNFun = try nonMonadicType
             <|> try unaryType
             <|> try constantType
             <|> parens typeP
             <|> tyVar
      where
        constantType = do
          ns <- getState
          n <- identifier ident'
          case lookup n [ (m,c) | (c@(TypeName m),0) <- ns ] of
           Nothing -> fail ("type constant '" ++ n ++ "'")
           Just c -> return (TyCon c [])
        unaryType = do
          ns <- getState
          a <- try constantType <|> parens typeP <|> tyVar
          n <- identifier ident'
          case lookup n [ (m,c) | (c@(TypeName m),1) <- ns ] of
           Nothing -> fail ("type unary '" ++ n ++ "'")
           Just c -> return (TyCon c [a])
        nonMonadicType = do
          ns <- getState
          as <- parens (typeP `sepBy1` symbol ",")
          n <- identifier ident'
          case lookup n [ (m,c) | (c@(TypeName m),a) <- ns, a == length as ] of
           Nothing -> fail ("type unary '" ++ n ++ "'")
           Just c -> return (TyCon c as)

datatypeDeclP :: Parser TypeDecl
datatypeDeclP = do
  symbol "type"
  vs <- varList <?> "type variable list"
  n <- TypeName <$> identifier ident'
  symbol "="
  modifyState ((n,length vs) :)
  cs <- (tyCase <?> "type case") `sepBy1` symbol "|" <?> "type declaration rhs"
  symbol ";;"  
  return (TypeDecl n vs cs)
    where
      varList = ((: []) <$> typeVarP) <|> parens (typeVarP `sepBy` symbol ",") <|> return []
      tyCase = (,) <$> constructor <*> tyList where
        tyList = (try (symbol "of") >> typeP `sepBy1` symbol "*")
                 <|> return []

funDeclP :: Parser FunDecl
funDeclP = do
      pos <- posP
      try (symbol "let")
      con <- try (symbol "rec" >> return FunDeclRec) <|> return FunDeclLet
      ls <- bindings `sepBy1` symbol "and"
      symbol ";;"
      return (con pos ls)
      where
        bindings = do
          pos <- posP
          (v:vs) <- many1 variable
          symbol "="
          e <- expP
          return (pos, v, vs, e)

programP :: Parser Program
programP = toProg <$> many1 ((Left <$> try (datatypeDeclP <?> "type declaration"))
                             <|> (Right <$> funDeclP <?> "function declaration"))
  where toProg = uncurry Program . partitionEithers
  

parseFromString :: Parser a -> String -> String -> Either String a
parseFromString parser source input =
  case runParser p [] source input of
   Left e -> Left (show e)
   Right r -> Right r
  where p = do {_ <- many (try comment <|> whiteSpace1); t <- parser; eof; return t }

expressionFromString :: String -> String -> Either String Exp
expressionFromString = parseFromString expP

programFromString :: String -> String -> Either String Program
programFromString = parseFromString programP
