module Main where

import FragTest

test :: ()
test = 
    want (pKnownFragCard (pNil .+ p1))
  `seq`
    want (pSetFrag (pNil .+ p2))
  `seq`
    ()

main :: IO ()
main = pure ()
