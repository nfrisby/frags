module Main where

import FragTest

test :: ()
test = [ pNil , pNil .+ p1 ]
  `seq`
    ()

main :: IO ()
main = pure ()
