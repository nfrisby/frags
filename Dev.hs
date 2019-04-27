{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{-# LANGUAGE FlexibleContexts #-}

{-# OPTIONS_GHC -Wall -Werror #-}
{-# OPTIONS_GHC -Wwarn=partial-type-signatures #-}

{-# OPTIONS_GHC -dcore-lint #-}
{-# OPTIONS_GHC -fplugin=Data.Frag.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Data.Frag.Plugin:trace #-}

-- {-# OPTIONS_GHC -fprint-explicit-kinds #-}
-- {-# OPTIONS_GHC -dppr-debug -dsuppress-all #-}
-- {-# OPTIONS_GHC -ddump-tc-trace #-}

module Dev where

import Data.Frag
import Data.Type.Equality ((:~:)(..),testEquality)

-- weaken :: ('() ~ SetFrag p,FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p)) => TIS p f -> proxy a -> TIS (p :+ a) f
-- weaken (MkTIS MkFragRep x) _ = MkTIS MkFragRep x

data TIS :: Frag k -> (k -> *) -> * where
  MkTIS :: FragRep p a -> f a -> TIS p f

box :: f a -> TIS ('Nil :+ a) f
box = inject

unbox :: TIS ('Nil :+ a) f -> f a
unbox (MkTIS MkFragRep x) = x

inject :: ('() ~ SetFrag p,FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p)) => f a -> TIS (p :+ a) f
inject = MkTIS MkFragRep

project :: ('() ~ SetFrag p,FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p)) => TIS (p :+ a) f -> Maybe (f a)
project = \(MkTIS frep x) -> co x <$> testEquality frep MkFragRep
  where
  co :: f a -> a :~: b -> f b
  co x Refl = x

-----

data F a = MkF{getF :: a}
  deriving (Show)

ex1 :: _
ex1 = box $ MkF True

ex2 :: TIS ('Nil :+ Char :+ Bool) F
ex2 = inject $ MkF True

ex3 :: TIS ('Nil :+ Bool :+ Char) F
ex3 = inject $ MkF 'a'

ex4 :: _ => _
ex4 = inject $ MkF 'c'

test1 :: Show a => Maybe (F a) -> IO ()
test1 = print . fmap getF

main :: IO ()
main = do
  let
    exs = [ex2,ex3,ex4]
  putStrLn "--- Abelian"
  print $ length exs
  putStrLn "--- Inference"
  print $ getF (unbox ex1)
  test1 $ project ex1
  putStrLn "--- Type-directed"
  mapM_ (test1 @Bool . project) exs
  mapM_ (test1 @Char . project) exs
