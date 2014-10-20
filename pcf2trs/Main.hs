module Main where
import           Control.Applicative ((<$>))
import           Control.Monad (foldM)
import qualified Hoca.FP as FP
import qualified Hoca.PCF as PCF
import           Hoca.PCF2Atrs (simplify, toProblem, prettyProblem)
import           System.Environment (getArgs)
import           System.Exit (exitFailure)
import           System.IO (hPutStrLn, stderr)
import           Text.PrettyPrint.ANSI.Leijen (Doc, renderSmart, Pretty (..), displayS)
import Data.Maybe (fromJust)

putDocLn :: Doc -> IO ()
putDocLn e = putStrLn (render e "")
  where render = displayS . renderSmart 1.0 80

putErrLn :: String -> IO ()
putErrLn = hPutStrLn stderr

normalise :: (PCF.Exp l -> Maybe (PCF.Exp l)) -> PCF.Exp l -> PCF.Exp l
normalise rel = fromJust . PCF.nf rel

expressionFromArgs :: FilePath -> [String] -> IO (PCF.Exp String)
expressionFromArgs fname args = do
  r <- mk <$> readFile fname
  case r of
   Left e -> putErrLn e >> exitFailure
   Right pcf -> return pcf
  where
    mk s = do
      fun <- normalise (PCF.ctxtClosure PCF.beta) <$> fromString fname s
      foldM (\ p (i,si) -> PCF.App p <$> fromString ("argument " ++ show i) si)
        fun (zip [(1::Int)..] args)
    fromString src str = FP.expFromString src str >>= FP.toPCF

helpMsg :: String
helpMsg = "pcf2trs [--eval|--pcf|--no-simp|--num-simps <nat>] <file> [args]*"

main :: IO ()
main = do
  args <- getArgs  
  case args of
   "--help" : _ -> putStrLn helpMsg
   "--eval" : fname : as -> do
     e <- expressionFromArgs fname as
     putDocLn (pretty (normalise PCF.cbv e))
   "--pcf" : fname : as -> do
     e <- expressionFromArgs fname as
     putDocLn (pretty e)
   "--no-simp" : fname : as -> do
     e <- expressionFromArgs fname as
     putDocLn (prettyProblem (toProblem e))
   "--num-simps" : i : fname : as -> do
     e <- expressionFromArgs fname as
     putDocLn (prettyProblem (simplify (Just (read i)) (toProblem e)))
   fname : as -> do
     e <- expressionFromArgs fname as
     putDocLn (prettyProblem (simplify Nothing (toProblem e)))
   _ -> error helpMsg

