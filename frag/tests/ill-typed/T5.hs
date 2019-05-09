{-# OPTIONS_GHC -Werror #-}

module Main where

import FragTest

test ::   -- demonstrates limited evaluation contexts
    proxy '(q,a,b)
  ->
    SetFrag (q :+ a) :~: SetFrag (q :- b :+ b :+ a)
test _ = Refl

main :: IO ()
main = pure ()
