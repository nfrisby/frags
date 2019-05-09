{-# OPTIONS_GHC -Werror #-}

module Main where

import FragTest

test :: ()   -- once triggered bug in Frag.interpret
test = [ pNil , pFragNE pChar (pFragNE pBool (pNil .- pBool)) ]
  `seq`
  ()

main :: IO ()
main = pure ()
