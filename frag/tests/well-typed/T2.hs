module Main where

import FragTest

test :: ()
test =
    fragCard (Proxy :: Proxy (FragLT 1 ('Nil :+ 1 :+ 2)))
  `seq`
    fragCard (Proxy :: Proxy (FragLT 2 ('Nil :+ 1 :+ 2)))
  `seq`
    fragCard (Proxy :: Proxy (FragLT 1 ('Nil :+ 2 :+ 1)))
  `seq`
    fragCard (Proxy :: Proxy (FragLT 2 ('Nil :+ 2 :+ 1)))
  `seq`
    ()

main :: IO ()
main = pure ()
