{-# OPTIONS_GHC -Werror #-}

module Main where

import FragTest

main :: IO ()
main = pure ()

-- This signature is ambiguous without the plugin.
test :: Proxy fr -> Proxy (fr :+ x)
test = \_ -> Proxy
