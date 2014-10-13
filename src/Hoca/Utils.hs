-- | 

module Hoca.Utils where

import Control.Applicative
import Control.Monad
import Control.Monad.State.Lazy as State

data VSState v =
  VSState { vsDefault :: v
          , vsSucc :: v -> v}
                 
newtype VariableSupply v r =
  VariableSupply { runSup :: State.State (VSState v) r }
  deriving (Applicative, Monad, Functor, State.MonadState (VSState v))
                             
runSupply :: VariableSupply v a -> v -> (v -> v) -> a
runSupply m v suc = State.evalState  (runSup m) (VSState v suc)

newVar :: VariableSupply v v
newVar = do
  VSState v suc <- State.get
  undefined
