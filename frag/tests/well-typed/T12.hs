{-# OPTIONS_GHC -Werror #-}

module Main where

import FragTest

test ::   -- once triggered insufficient subst
    prp p -> prq p -> pra a -> prb b
  ->
    (q :+ a) :~: (p :+ b)
  ->
    (p :- a :+ b) :~: q
test _ _ _ _ Refl = Refl

main :: IO ()
main = pure ()
