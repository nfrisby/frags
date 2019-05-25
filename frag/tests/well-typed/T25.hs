module Main where

import FragTest25

main :: IO ()
main = pure ()

-----

-- for some reason, the T26 bug only triggers in the instance declaration

test :: Proxy (l :: k -> *) -> ()
test l =
    (let c = pSetFrag (pSumFrag l) in give c $ want c)
  `seq`
    ()

test2 :: (SetFrag (SumFrag l) ~ '()) => Proxy (l :: k -> *) -> ()
test2 l =
    want (pSetFrag (pSumFrag l))
  `seq`
    ()
