module Main where

import FragTest

test :: Proxy (p :: Frag Nat) -> ()
test p = [ p , p .+ p1 ]
  `seq`
    ()

main :: IO ()
main = pure ()
