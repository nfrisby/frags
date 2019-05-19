module Main where

import FragTest

main :: IO ()
main = pure ()

-----
{-
-- tests the special multiplicity rule for :=
test :: (FragEQ k (DomFrag p) ~ 'Nil) => Proxy k -> Proxy (p :: Frag (Mapping Nat Symbol)) -> ()
test k p =
    [ pNil , pFragEQ (k .= pA) p ]
  `seq`
    ()
-}
