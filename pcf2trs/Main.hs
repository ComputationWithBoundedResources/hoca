module Main where
import qualified Hoca.PCF as PCF
import qualified Hoca.FP as FP
import System.Environment (getArgs)
import Text.PrettyPrint.ANSI.Leijen (renderSmart, Pretty (..), displayS)
import Control.Applicative ((<$>))
import Control.Monad (foldM)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

putPrettyLn :: Pretty e => e -> IO ()
putPrettyLn e = putStrLn (render e "")
  where render = displayS . renderSmart 1.0 80 . pretty

putErrLn :: String -> IO ()
putErrLn = hPutStrLn stderr

expressionFromArgs :: FilePath -> [String] -> IO PCF.Exp
expressionFromArgs fname args = do
  r <- mk <$> readFile fname
  case r of
   Left e -> putErrLn (show e) >> exitFailure
   Right p -> case FP.toPCF p of
     Left e -> putErrLn e >> exitFailure
     Right pcf -> return pcf          
  where
    mk s = do
      fun <- FP.expFromString fname s
      foldM (\ p (i,si) -> FP.App p <$> FP.expFromString ("argument " ++ show i) si)
        fun (zip [(1::Int)..] args)

main :: IO ()
main = do
  args <- getArgs  
  case args of
   "--eval" : fname : as -> do
     e <- expressionFromArgs fname as
     putPrettyLn (PCF.nf e)
   "--pcf" : fname : as -> do
     e <- expressionFromArgs fname as
     putPrettyLn e
   _ -> error "pcf2trs [--eval|--pcf] <file> [args]*"

