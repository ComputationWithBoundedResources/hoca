module Main where
import System.Environment (getArgs)
import Hoca.PCF
import System.Exit (exitWith)

main :: IO ()
main = do
  (fname:_) <- getArgs
  r <- expFromFile fname
  case r of
   Left e -> putStrLn (show e)
   Right e ->
     case expFromNamed e of
      Nothing -> putStrLn "given term not closed"
      Just e' ->
        putStrLn (show e')

