{-# OPTIONS_GHC -Werror #-}

module Main where

import FragTest

-- c.f. https://gitlab.haskell.org/ghc/ghc/issues/16639

test :: Is1or2 p -> Is1or2 p -> ()
test Is1 Is1 = ()
test Is2 Is2 = ()
test Is1 _ = ()
test Is2 _ = ()
test _ Is1 = ()
test _ Is2 = ()

main :: IO ()
main = pure ()
