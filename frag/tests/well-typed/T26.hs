{-# LANGUAGE FlexibleInstances #-}

module Main where

import FragTest25

main :: IO ()
main = pure ()

-----

-- caught a bug where the plugin discarded a Given CFunEqCan by reorienting it
instance (SetFrag (SumFrag l) ~ '()) => C l where
  method = want . pSetFrag . pSumFrag
