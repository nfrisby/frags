module Main where

import FragTest

-- This one is kind of hard to interrogate, but it has caught various bugs.
-- And those repros have usually only shrunk to hard-to-predict subsets of sublists of the lists.
eqs :: Proxy (x :: k) -> Proxy (y :: k) -> ()
eqs px py =
    [   pNil .+ px   ,   pNil .+ px .+ px .- px   ,   pNil .+ px .- px .+ px   ,   pNil .- px .+ px .+ px   ]
  `seq`
    [   pNil .+ px .+ py   ,   pNil .+ py .+ px   ]
  `seq`
    [   pNil .+ px .- py   ,   pNil .- py .+ px   ]
  `seq`
    [   pNil .- px .+ py   ,   pNil .+ py .- px   ]
  `seq`
    [   pNil .- px .- py   ,   pNil .- py .- px   ]
  `seq`
    [   pNil   ,   pNil .+ px .- px   ,   pNil .+ py .- py   ]
  `seq`
    ()

main :: IO ()
main = pure ()
