{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module Main where

import FragTest

main :: IO ()
main = pure ()

-----

type TheWanted =
  MonadState
    (Proxy ('Nil :+ "A" :+ "B"))
    (State (Proxy ('Nil :+ "B" :+ "A")))

-- solver diverges if we don't update the Wanted MonadState constraint;
-- its fundep emits (Proxy ('Nil :+ "A" :+ "B") ~ Proxy ('Nil :+ "B" :+ "A")),
-- we discard that as trivial,
-- and so on.
--
-- The plugin thus must canonicalize the frags in that constraint.
test :: ()
test =
    want (Proxy :: Proxy TheWanted)
  `seq`
    ()
