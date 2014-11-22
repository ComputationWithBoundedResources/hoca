module Main where
import           Control.Applicative ((<$>))
import           Control.Monad (foldM)
import qualified Hoca.FP as FP
import qualified Hoca.PCF as PCF
import qualified Hoca.Narrowing as N
import qualified Hoca.UsableRules as U
import qualified Hoca.ATRS as ATRS
import           Hoca.Transform
import           Hoca.PCF2Atrs (prettyProblem, signature)
import           System.Environment (getArgs)
import           System.IO (hPutStrLn, stderr)
import           Text.PrettyPrint.ANSI.Leijen (Doc, renderSmart, Pretty (..), displayS, (</>), (<+>), align, linebreak, indent, text)
import Data.Maybe (fromJust)
import qualified Data.Rewriting.Rule as R
import qualified Data.Rewriting.Term as T
import qualified Data.Rewriting.Problem as P
import System.Exit (exitSuccess,exitFailure)

expressionFromArgs :: FilePath -> [String] -> IO (PCF.Exp FP.Context)
expressionFromArgs fname args = do
  r <- mk <$> readFile fname
  case r of
   Left e -> putErrLn e >> exitFailure
   Right pcf -> return pcf
  where
    mk s = do
      fun <- fromString fname s
      foldM (\ p (i,si) -> PCF.App [] p <$> fromString ("argument " ++ show i) si)
        fun (zip [(1::Int)..] args)
    fromString src str = FP.expFromString src str >>= FP.toPCF


simplify :: Problem -> Maybe Problem
simplify =
  exhaustive (narrow caseRules >=> try usableRules >=> try neededRules)
  >=> dfaInstantiate hoHeadVariables
  >=> exhaustive (narrow nonRecursiveRules >=> try usableRules >=> try neededRules)
  where
    hoHeadVariables (R.rhs -> T.Var (v, _ :~> _)) = [v]
    hoHeadVariables trl = ATRS.headVars (R.rhs (ATRS.unTypeRule trl)) -- TODO: change TypedRule

    narrowedWith = map N.narrowedWith . N.narrowings
    caseRules _ = all isCaseRule . narrowedWith where
      isCaseRule (ATRS.headSymbol . R.lhs -> Just Cond {}) = True
      isCaseRule _ = False

    nonRecursiveRules rs = all (not . U.isRecursive rs) . narrowedWith

                           
transform :: Bool -> FilePath -> [String] -> IO ()
transform doSimp fname as = do
  e <- expressionFromArgs fname as  
  case tr e of
   Just prob -> putDocLn (prettyProblem (withSignature prob))
   Nothing -> do
     putErrLn "the program cannot be transformed"
     exitFailure
  where
    tr
      | doSimp = pcfToTrs >=> simplify
      | otherwise = pcfToTrs
                    
    withSignature prob = prob { P.comment = Just (displayS (renderSmart 1.0 75 cmt) "") }
      where cmt = 
              case signature prob of
               Left err -> text "The system is not typeable:" <+> text err
               Right s -> text "Types are as follows:"
                          </> linebreak
                          </> indent 5 (align (pretty s))
                          </> linebreak

helpMsg :: String
helpMsg = "pcf2trs [--eval|--pcf|--no-simp] <file> [args]*"

putDocLn :: Doc -> IO ()
putDocLn e = putStrLn (render e "")
  where render = displayS . renderSmart 1.0 80

putErrLn :: String -> IO ()
putErrLn = hPutStrLn stderr

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
     transform False fname as
   fname : as ->
     transform True fname as     
   _ -> error helpMsg
  exitSuccess


-- rulesFromFile :: FilePath -> IO [Data.Rewriting.Rule.Type.Rule (Hoca.ATRS.ASym Hoca.PCF2Atrs.Symbol) Hoca.PCF2Atrs.Var]
-- rulesFromFile fname = do
--   e <- expressionFromArgs fname []
--   return (P.allRules (P.rules (toProblem e)))
