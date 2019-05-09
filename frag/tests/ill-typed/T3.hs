{-# OPTIONS_GHC -Werror #-}

module Main where

import FragTest

test :: Is1or2 p -> Is1or2 p -> ()
test Is1 Is2 = ()
test _ _ = ()

main :: IO ()
main = pure ()
