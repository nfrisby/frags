module Main where

import FragTest

test :: proxy a -> proxy a1 -> q :~: (p1 :+ a1) -> FragLT a (p1 :+ a1) :~: 'Nil -> FragLT a q :~: 'Nil
test _ _ Refl Refl = Refl

main :: IO ()
main = pure ()
