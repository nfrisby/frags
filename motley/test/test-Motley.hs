{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -dcore-lint #-}
{-# OPTIONS_GHC -fplugin=Data.Frag.Plugin #-}

{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}

module Main where

import Control.Lens (over)
import qualified Data.Functor.HO as HO
import Data.Frag (FragRep(..))
import Data.Motley
import Data.Proxy (Proxy(..))

-----

ex1 :: _
ex1 = toSingletonSum $ Identity False

ex2 :: Sum ('Nil :+ Char :+ Bool) Identity
ex2 = inj $ Identity True

ex3 :: Sum ('Nil :+ Bool :+ Char) Identity
ex3 = inj $ Identity 'a'

ex4 :: _ => _
ex4 = toSingletonSum (Identity 'c') `plusSum` Proxy @Bool

test1 :: Show a => Maybe (Identity a) -> IO ()
test1 = mapM_ test2

test2 :: Show a => Identity a -> IO ()
test2 = print . runIdentity

ex5 :: _
ex5 = nil `ext` Identity True `ext` Identity 'z' `ext` Identity (3 :: Int)

ex6 :: _
ex6 = nil `ext` Identity True `ext` Identity 'z'

-----

partitionSums :: (Foldable t,AllProd None p)  => t (Sum p f) -> Prod p (Compose [] f)
partitionSums = foldr cons (HO.pure (Compose []))
  where
  cons :: Sum p f -> Prod p (Compose [] f) -> Prod p (Compose [] f)
  cons (MkSum MkFragRep x) = over opticProd (\(Compose xs) -> Compose (x : xs))

-----

main :: IO ()
main = do
  let
    exs = [ex1 `plusSum` Proxy @Char,ex2,ex3,ex4]
  putStrLn "--- Sums"
  print exs
  putStrLn "--- Prods"
  print ex5
  print ex6

  putStrLn "--- Inference"
  print $ runIdentity (fromSingletonSum ex1)
  test1 $ HO.toMaybe ex1

  putStrLn "--- HO.toMaybe Bool"
  mapM_ (test1 @Bool . HO.toMaybe) exs
  putStrLn "--- HO.toMaybe Char"
  mapM_ (test1 @Char . HO.toMaybe) exs

  putStrLn "--- Sum absurd and alternative"
  flip mapM_ exs $ absurd "top" `alt` (print @Bool . runIdentity) `alt` (print @Char . runIdentity)

  putStrLn "--- Prod projection"
  test2 @Bool $ prj ex5
  test2 @Char $ prj ex5
  test2 @Int $ prj ex5

  putStrLn "--- Prod retraction"
  let
    (r1,x1) = ret ex5
    (r2,x2) = ret r1
    (r3,x3) = ret r2
    _ascribe = r3 `asTypeOf` nil
  test2 @Bool x1
  test2 @Char x2
  test2 @Int x3

  putStrLn "--- elimProdSum"
  let
    mk f = Compose $ Op $ f . runIdentity
    prints = nil `ext` mk (print @Bool) `ext` mk (print @Char)
  prints `elimProdSum` ex4

  putStrLn "--- dictProd"
  let
    printD :: Dict1 Show a -> Compose (Op (IO ())) Identity a
    printD = \Dict1 -> mk print
  mapProd printD dictProd `elimProdSum` ex4
