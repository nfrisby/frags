module Main where

import FragTest

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
