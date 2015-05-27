#!/usr/bin/runhaskell

module Main where

import System.Environment (getArgs)
import Data.Char (toUpper,isLower)

translate :: String -> String
translate = foldr (\ t r -> "Cons("++t++","++r++")") "Nil" . map toToken
  where toToken '\\' = "SLASH"
        toToken '(' = "LPAREN"
        toToken ')' = "RPAREN"
        toToken '.' = "DOT"                      
        toToken '-' = "MINUS"                      
        toToken '>' = "GT"
        toToken ' ' = "SPACE"
        toToken a | isLower a = [toUpper a]
        toToken a = [a]

main :: IO ()
main = do
  a:_ <- getArgs
  putStr (translate a)
  
