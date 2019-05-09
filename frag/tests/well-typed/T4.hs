module Main where

import FragTest

infer1 :: ('() ~ SetFrag p,FragEQ 1 p ~ ('Nil :+ '() :- '() :+ '())) => Proxy p -> ()
infer1 pp =
    want (pSetFrag (pp .- p1))
  `seq`
    want (pSetFrag (pFragEQ p1 (pNil .+ p2)))
  `seq`
    ()

main :: IO ()
main = pure ()
