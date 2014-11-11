module Main where
import           Control.Applicative ((<$>))
import           Control.Monad (foldM)
import qualified Hoca.FP as FP
import qualified Hoca.PCF as PCF
import           Hoca.PCF2Atrs (simplify, toProblem, prettyProblem, signature)
import           System.Environment (getArgs)
import           System.IO (hPutStrLn, stderr)
import           Text.PrettyPrint.ANSI.Leijen (Doc, renderSmart, Pretty (..), displayS, (</>), (<+>), align, linebreak, indent, text)
import Data.Maybe (fromJust)
import qualified Data.Rewriting.Problem as P
import System.Exit (exitSuccess,exitFailure)

putDocLn :: Doc -> IO ()
putDocLn e = putStrLn (render e "")
  where render = displayS . renderSmart 1.0 80

putErrLn :: String -> IO ()
putErrLn = hPutStrLn stderr

expressionFromArgs :: FilePath -> [String] -> IO (PCF.Exp String)
expressionFromArgs fname args = do
  r <- mk <$> readFile fname
  case r of
   Left e -> putErrLn e >> exitFailure
   Right pcf -> return pcf
  where
    mk s = do
      fun <- fromString fname s
      foldM (\ p (i,si) -> PCF.App p <$> fromString ("argument " ++ show i) si)
        fun (zip [(1::Int)..] args)
    fromString src str = FP.expFromString src str >>= FP.toPCF


transform :: Bool -> Maybe Int -> FilePath -> [String] -> IO ()
transform doSimp nt fname as = do
  e <- expressionFromArgs fname as  
  case probFromExpression e of
   Just prob -> putDocLn (prettyProblem (withSignature prob))
   Nothing -> do
     putErrLn "the program cannot be transformed"
     exitFailure
  where
    probFromExpression e
      | doSimp = simplify nt (toProblem e)
      | otherwise = Just (toProblem e)
                    
    withSignature prob = prob { P.comment = Just (displayS (renderSmart 1.0 75 cmt) "") }
      where cmt = 
              case signature prob of
               Left err -> text "The system is not typeable:" <+> text err
               Right s -> text "Types are as follows:"
                          </> linebreak
                          </> indent 5 (align (pretty s))
                          </> linebreak

helpMsg :: String
helpMsg = "pcf2trs [--eval|--pcf|--no-simp|--num-simps <nat>] <file> [args]*"

main :: IO ()
main = do
  args <- getArgs  
  case args of
   "--help" : _ -> putStrLn helpMsg
   "--eval" : fname : as -> do
     e <- expressionFromArgs fname as
     putDocLn (pretty (fromJust (PCF.nf PCF.cbv e)))
   "--pcf" : fname : as -> do
     e <- expressionFromArgs fname as
     putDocLn (pretty e)
   "--no-simp" : fname : as -> 
     transform False Nothing fname as
   "--num-simps" : i : fname : as -> 
     transform True (Just (read i)) fname as
   fname : as ->
     transform True Nothing fname as     
   _ -> error helpMsg
  exitSuccess


rulesFromFile fname = do
  e <- expressionFromArgs fname []
  return (P.allRules (P.rules (toProblem e)))
