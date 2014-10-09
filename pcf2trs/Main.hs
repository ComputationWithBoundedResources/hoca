module Main where
import           Control.Applicative ((<$>))
import           Control.Monad (foldM)
import qualified Hoca.FP as FP
import qualified Hoca.PCF as PCF
import           Hoca.PCF2Trs (toProblem, prettyProblem)
import           System.Environment (getArgs)
import           System.Exit (exitFailure)
import           System.IO (hPutStrLn, stderr)
import           Text.PrettyPrint.ANSI.Leijen (Doc, renderSmart, Pretty (..), displayS)

putDocLn :: Doc -> IO ()
putDocLn e = putStrLn (render e "")
  where render = displayS . renderSmart 1.0 80

putErrLn :: String -> IO ()
putErrLn = hPutStrLn stderr

expressionFromArgs :: FilePath -> [String] -> IO PCF.Exp
expressionFromArgs fname args = do
  r <- mk <$> readFile fname
  case r of
   Left e -> putErrLn e >> exitFailure
   Right pcf -> return pcf
  where
    mk s = do
      fun <- PCF.nf PCF.beta <$> fromString fname s
      foldM (\ p (i,si) -> PCF.App p <$> fromString ("argument " ++ show i) si)
        fun (zip [(1::Int)..] args)
    fromString src str = FP.expFromString src str >>= FP.toPCF
    
main :: IO ()
main = do
  args <- getArgs  
  case args of
   "--eval" : fname : as -> do
     e <- expressionFromArgs fname as
     putDocLn (pretty (PCF.nf PCF.cbv e))
   "--pcf" : fname : as -> do
     e <- expressionFromArgs fname as
     putDocLn (pretty e)
   fname : as -> do
     e <- expressionFromArgs fname as
     putDocLn (prettyProblem (toProblem e))
   _ -> 
     error "pcf2trs [--eval|--pcf] <file> [args]*"

