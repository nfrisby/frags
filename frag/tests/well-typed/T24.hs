module Main where

import FragTest

main :: IO ()
main = pure ()

-----

-- Row.rmv does not need its @Proxy lbl@ argument.
test1 :: (FragEQ (lbl := a) p ~ 'Nil,KnownFragCard (FragLT (lbl := a) p)) => Proxy (p :+ lbl := a) -> Proxy p
test1 = undefined

-- Row.prj does need its @Proxy lbl@ argument, but not @Proxy a@
test2 :: (FragEQ (lbl := a) p ~ 'Nil,KnownFragCard (FragLT (lbl := a) p)) => Proxy lbl -> Proxy (p :+ lbl := a) -> a
test2 = undefined
