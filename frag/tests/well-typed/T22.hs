module Main where

import FragTest

main :: IO ()
main = pure ()

-----

-- special multiplicity rule for :=
test :: ()
test =
    want (pA `isEq` popK p1 (pNil .+ p1 .= pA))
  `seq`
    ()
