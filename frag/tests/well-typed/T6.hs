module Main where

import FragTest

main :: IO ()
main = pure ()

infer2 :: KnownFragCard (FragEQ a ('Nil :+ b :+ a)) => Proxy a -> Proxy b -> ()
infer2 pa pb =
    want (pKnownFragCard $ pFragEQ pa $ pNil .+ pb)
  `seq`
    ()

