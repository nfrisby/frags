module Main where

import FragTest

main :: IO ()
main = pure ()

-----

-- Row.prj does need its @Proxy lbl@ argument.
test :: (FragEQ (lbl := a) p ~ 'Nil,KnownFragCard (FragLT (lbl := a) p)) => Proxy (p :+ lbl := a) -> a
test = undefined
