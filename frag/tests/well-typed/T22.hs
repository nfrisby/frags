module Main where

import FragTest

main :: IO ()
main = pure ()

-----

-- special multiplicity rule for :=
--
-- Once caught a bug where TcUnify.metaTyVarUpdateOK prevented assignments
-- because the RHS had :+ and/or :- in it.
test :: ()
test =
    want (pA `isEq` popK p1 (pNil .+ p1 .= pA))
  `seq`
    ()
