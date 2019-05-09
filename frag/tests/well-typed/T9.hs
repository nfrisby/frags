{-# OPTIONS_GHC -Werror #-}

module Main where

import FragTest

test ::   -- once triggered unnecessary swapping
     proxyp p1 -> proxya a1
   ->
     q :~: (p1 :+ a1)
   ->
     ()
test _ _ Refl = ()

main :: IO ()
main = pure ()
