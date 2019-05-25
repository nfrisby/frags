{-# LANGUAGE FlexibleContexts #-}

module Main where

import FragTest

main :: IO ()
main = pure ()

-----

-- fails the ambiguity check if the MonadState fundep's Derived is ignored
test ::
    (FragEQ Int p ~ 'Nil,MonadState (Proxy (p :+ Int)) m)
  =>
    Proxy f -> m ()
test = undefined
