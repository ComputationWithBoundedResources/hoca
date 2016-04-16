{-# LANGUAGE ViewPatterns, TypeOperators, FlexibleContexts, DeriveDataTypeable #-}
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
import           Hoca.Transform as T
import           Hoca.Utils (putDocLn)
import           System.Environment (getArgs)
import           System.Exit (exitSuccess,exitFailure)
import           System.IO (hPutStrLn, stderr)
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import System.Console.CmdArgs

type Problem f = P.Problem f Int

transform = try simplifyATRS >=> toTRS >=> try simplify >=> try compress

data Pcf2Trs = Eval { fname :: FilePath
                    , call :: String }
             | Pcf { fname :: FilePath
                   , call :: String }
             | Defunctionalise { fname :: FilePath
                               , call :: String}
             | Translate { fname :: FilePath
                         , call :: String }
          deriving (Show, Data, Typeable)

translate :: Pcf2Trs
translate = Translate
  { fname = def &= argPos 0 &= typFile 
  , call = def &= argPos 1  &= typ "PCF-expression"  &= opt ""}

eval :: Pcf2Trs
eval = Eval
  { fname = def &= argPos 2 &= typFile 
  , call = def &= argPos 3  &= typ "PCF-expression"  &= opt ""
  }

defunc :: Pcf2Trs
defunc = Defunctionalise
  { fname = def &= argPos 4 &= typFile 
  , call = def &= argPos 5  &= typ "PCF-expression"  &= opt ""
  }

pcf :: Pcf2Trs
pcf = Pcf
  { fname = def &= argPos 6 &= typFile 
  , call = def &= argPos 7 &= typ "PCF-expression"  &= opt ""
  }


mode = modes [pcf,eval,defunc,translate] &= help "Translate Ocaml programs to TRSs" &= program "pcf2trs" &= summary "Translate Ocaml programs to TRSs"

main :: IO ()
main = do
  cfg <- cmdArgs mode
  p <- programFromArgs cfg
  case cfg of
    Eval {} -> putDocLn (PP.pretty (fromJust (PCF.nf PCF.cbv (PCF.expression p))))
    Pcf {} -> typeProgram p >>= putDocLn
    Translate {} -> 
      typeProgram p >>= defunctionalizeProgram >>= simplifyAtrs >>= displayTrs
    Defunctionalise {} -> 
      typeProgram p >>= defunctionalizeProgram >>= displayTrs
  exitSuccess      
  where
    programFromArgs cfg = do
      s <- readFile (fname cfg)
      case programFromString (fname cfg) s >>= desugar' of
        Left e -> putStrLn e >> exitFailure
        Right p -> return p
     where
       desugar' | null (call cfg) = desugar Nothing
                | otherwise = desugar (Just (call cfg))
    typeProgram p = case DM.infer p of 
       Left e -> putDocLn (PP.pretty p) >> putDocLn (PP.pretty e) >> exitFailure
       Right p' -> return p'
    defunctionalizeProgram p = case run defunctionalize p of 
        Nothing -> putStrLn "defunctionalization failed" >> exitFailure
        Just p' -> return p'
    simplifyAtrs p = case run transform p of 
        Nothing -> putStrLn "simplification failed" >> exitFailure
        Just p' -> return p'
    displayTrs :: (Eq f, PP.Pretty f) => Problem f -> IO ()
    displayTrs = putDocLn . prettyWST
