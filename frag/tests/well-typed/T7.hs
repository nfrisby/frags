module Main where

import FragTest

test :: ()
test =
    [ pNil .+ p1 .+ p2 , pNil .+ p2 .+ p1 ]
  `seq`
    ()

main :: IO ()
main = pure ()
