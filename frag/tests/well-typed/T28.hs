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
--
-- Maybe GHC should not emit the same fundep equality multiple times?
-- I suppose that would require each constraint to track which top-level instances it has already interacted with in that way,
-- and to forget that set whenever the constraint "significantly changes", etc. Sounds tedious!
test :: ()
test =
    want (Proxy :: Proxy TheWanted)
  `seq`
    ()
