{-# OPTIONS_GHC -Werror #-}

module Main where

import FragTest

unboxS ::   -- once triggered insufficient swapping ('Nil ~ FragEQ ...) instead of (FragEQ ... ~ 'Nil)
  FragRep ('Nil :+ a) b -> f b -> f a
unboxS = \MkFragRep x -> x

main :: IO ()
main = pure ()
