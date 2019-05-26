{-# OPTIONS_GHC -dcore-lint #-}
{-# OPTIONS_GHC -fplugin=Data.Frag.Plugin #-}

-- {-# OPTIONS_GHC -fconstraint-solver-iterations=20 #-}

-- {-# OPTIONS_GHC -fplugin-opt Data.Frag.Plugin:trace #-}
-- {-# OPTIONS_GHC -ddump-tc-trace #-}

module Main where

import Control.Lens (over)
import Control.Lens.Wrapped (_Wrapped,_Wrapping)
import Control.Monad.State
import Data.Motley

import AuxMTLState

main :: IO ()
main =
  flip evalStateT s0 $ do
  get >>= liftIO . print
  modify $ over opticProd' $ Identity . MkA . (+1) . getA . runIdentity
  modify $ over (opticProd' . _Wrapped) $ MkA . (+1) . getA
  modify $ over (opticProd' . _Wrapped . _Wrapping MkA) $ (+1)
  get >>= liftIO . print
  modify $ over (opticProd' . _Wrapped . _Wrapping MkB) $ (:) "hi"
  get >>= liftIO . print
  pure ()
