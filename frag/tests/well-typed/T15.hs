{-# OPTIONS_GHC -Werror #-}

module Main where

import FragTest

test :: Proxy (x :: Frag *) -> ()
test px = [ pFragNE pChar (pFragNE pBool px) , pFragNE pChar (pFragNE pBool (px .- pBool)) ]
  `seq`
  ()

main :: IO ()
main = pure ()
