{-# OPTIONS_GHC -Werror #-}

module Main where

import FragTest

test ::   -- once triggered insufficient swapping
    proxyp p1 -> proxya a1
  ->
    q :~: (p1 :+ a1)
  ->
    (q :- a1) :~: p1
test _ _ Refl = Refl

main :: IO ()
main = pure ()
