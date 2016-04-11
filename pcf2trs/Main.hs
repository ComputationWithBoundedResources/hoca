{-# LANGUAGE ViewPatterns, TypeOperators, FlexibleContexts #-}
#!/usr/local/bin/runhaskell
module Main where


import           Control.Applicative
import           Data.Maybe (fromJust)
import           Hoca.Data.Symbol
import qualified Hoca.PCF.Core as PCF
import qualified Hoca.PCF.Core.DMInfer as DM
import           Hoca.PCF.Desugar (desugar, desugarExpression)
import           Hoca.PCF.Sugar (programFromString, expressionFromString, Context)
import qualified Hoca.Problem as P
import           Hoca.Problem hiding (Problem,TRule)
import           Hoca.Transform
import           Hoca.Utils (putDocLn)
import           System.Environment (getArgs)
import           System.Exit (exitSuccess,exitFailure)
import           System.IO (hPutStrLn, stderr)
import qualified Text.PrettyPrint.ANSI.Leijen as PP


type Problem f = P.Problem f Int
type ATRS = Problem Symbol
type TRS = Problem TRSSymbol
type TRule = P.TRule Symbol Int


transform :: ATRS :=> TRS
transform = try simplifyATRS >=> toTRS >=> try simplify >=> try compress

programFromArgs :: FilePath -> Maybe String -> [String] -> IO (PCF.Program Context)
programFromArgs fname mname args = do
  r <- parseDesugared <$> readFile fname
  either (\e -> putErrLn e >> exitFailure) return r where
    parseDesugared s = do
      p <- programFromString fname s >>= desugar mname
      as <- sequence [ expressionFromString ("argument " ++ show i) ai >>= desugarExpression
                     | (i,ai) <- zip [(1::Int)..] args]
      return p { PCF.expression = foldl (PCF.App mempty) (PCF.expression p) as }

programFromFile :: FilePath -> IO (PCF.Program Context)
programFromFile fname = programFromArgs fname Nothing []

defunctionalizedFromFile :: FilePath -> Maybe String -> [String] -> IO ATRS
defunctionalizedFromFile fn m a = do
  prog <- programFromArgs fn m a 
  case DM.infer prog of 
    Left e -> putDocLn e >> error "Typing failed!"
    Right prog' -> 
      case run defunctionalize prog' of 
        Nothing -> error "Defunctionalization failed!"
        Just p -> return p

-- Main
    
helpMsg :: String
helpMsg = "pcf2trs [--eval|--pcf|--no-simp] <file> [args]*"

putErrLn :: String -> IO ()
putErrLn = hPutStrLn stderr

main :: IO ()
main = do
  as <- getArgs  
  case as of
   "--help" : _ -> putStrLn helpMsg
   "--eval" : fname : as' -> do
     e <- PCF.expression <$> programFromArgs fname Nothing as'
     putDocLn (PP.pretty (fromJust (PCF.nf PCF.cbv e)))
   "--eval" : _ -> putStrLn helpMsg
   "--pcf" : fname : [] -> do
     p <- programFromArgs fname Nothing []
     case DM.infer p of 
       Left e -> putDocLn (PP.pretty p) >> putDocLn e
       Right p' -> putDocLn (PP.pretty p')
   "--pcf" : _ -> putStrLn helpMsg     
   "--no-simp" : fname : [] -> 
     trans False fname Nothing
   "--no-simp" : fname : name : [] -> 
     trans False fname (Just name)
   "--no-simp" : _ -> putStrLn helpMsg          
   fname : []  ->
     trans True fname Nothing
   fname : args  ->
     trans True fname (Just (concat args))
   _ -> error helpMsg
  exitSuccess
  where
    trans True fname mname = do
      prob <- defunctionalizedFromFile fname mname []
      case run transform prob of
        Nothing -> do
         putErrLn "the program cannot be transformed"
         exitFailure
        Just res -> putDocLn (prettyWST res)
    trans False fname mname = do
      prob <- defunctionalizedFromFile fname mname []
      putDocLn (prettyWST prob)
