{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{-# LANGUAGE FlexibleContexts #-}

{-# OPTIONS_GHC -Wall -Werror #-}
{-# OPTIONS_GHC -Wwarn=partial-type-signatures #-}

{-# OPTIONS_GHC -dcore-lint #-}
{-# OPTIONS_GHC -fplugin=Data.Frag.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Data.Frag.Plugin:trace #-}

{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}

-- {-# OPTIONS_GHC -fprint-explicit-kinds #-}
-- {-# OPTIONS_GHC -dppr-debug -dsuppress-all #-}
-- {-# OPTIONS_GHC -ddump-tc-trace #-}

module Dev where

import Data.Frag
import Data.Proxy (Proxy(..))
import Data.Type.Equality ((:~:)(..))

import Unsafe.Coerce (unsafeCoerce)

data TIS :: Frag k -> (k -> *) -> * where
  MkTIS :: FragRep p a -> f a -> TIS p f

inj :: (FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p)) => f a -> TIS (p :+ a) f
inj = MkTIS MkFragRep

-- | Build @+1@
emb :: ('() ~ SetFrag p,FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p)) => TIS p f -> proxy a -> TIS (p :+ a) f
emb = \(MkTIS old x) _ -> MkTIS (widenFragRep old MkFragRep) x

-- | Consume @0@
absurd :: String -> TIS 'Nil f -> a
absurd = \s _ -> error $ "absurd TIS: " ++ s

-- | Consume @+1@
alt :: ('() ~ SetFrag p,FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p)) => (TIS p f -> ans) -> (f a -> ans) -> TIS (p :+ a) f -> ans
alt = \inner here (MkTIS old x) -> case narrowFragRep old MkFragRep of
  Left refl -> here $ co x refl
  Right new -> inner $ MkTIS new x
  where
  co :: f a -> a :~: b -> f b
  co x Refl = x

boxS :: f a -> TIS ('Nil :+ a) f
boxS = inj

unboxS :: TIS ('Nil :+ a) f -> f a
unboxS = \(MkTIS MkFragRep x) -> x

toMaybe :: ('() ~ SetFrag p,FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p)) => TIS (p :+ a) f -> Maybe (f a)
toMaybe = const Nothing `alt` Just

-----

data TIP :: Frag k -> (k -> *) -> * where
  MkCons :: !(FragRep (p :+ j) j) -> !(TIP p f) -> f a -> TIP (p :+ j) f
  MkNil :: TIP 'Nil f

setTIP :: TIP fr f -> '() :~: SetFrag fr
setTIP tip = tip `seq` unsafeCoerce Refl   -- simple inductive proof

-- | Build @0@
nil :: TIP 'Nil f
nil = MkNil

-- | Build @+1@
ext :: forall a p f. ('() ~ SetFrag p,FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p)) => TIP p f -> f a -> TIP (p :+ a) f
--ext = MkCons MkFragRep
ext = \tip x -> go tip MkFragRep x
  where
  go :: forall q. TIP q f -> FragRep (q :+ a) a -> f a -> TIP (q :+ a) f
  go tip new x = case tip of
    MkCons old inner y -> case extCase of
      Here -> MkCons new tip x
      Inside new' old' -> MkCons old' (go inner new' x) y
      where
      extCase = steer (case (new,old,setTIP inner,setTIP tip) of (MkFragRep,MkFragRep,Refl,Refl) -> Refl) new old
    MkNil -> MkCons new MkNil x

data ExtCase :: Frag k -> k -> k -> * where
  Here :: ExtCase p a b
  Inside :: !(FragRep (p :- b :+ a) a) -> !(FragRep (p :+ a) b) -> ExtCase p a b

steer :: forall p a b. '() :~: SetFrag p -> FragRep (p :+ a) a -> FragRep p b -> ExtCase p a b
steer pset new old
  | fragRepZ new < fragRepZ old' = Here
  | otherwise = Inside new' old'
  where
  old' = case pset of Refl -> widenFragRep old new

  apt :: a :/~: b
  apt = case (new,old) of (MkFragRep,MkFragRep) -> apartByFragEQ01 (Proxy @p) (Proxy @a) (Proxy @b)

  new' :: FragRep (p :- b :+ a) a
  new' = case (new,old,old',pset,apt) of (MkFragRep,MkFragRep,MkFragRep,Refl,MkApart) -> narrowFragRep' apt new old'

test :: TIP p f -> [Int]
test = \case
  MkCons frep c _ -> fragRepZ frep : test c
  MkNil -> []

testX1 :: [Int]
testX1 = test $ nil `ext` MkF True `ext` MkF 'a' `ext` MkF (0 :: Int)

testX2 :: [Int]
testX2 = test $ nil `ext` MkF (0 :: Int) `ext` MkF 'a'

-- | Consume @+1@
prj :: ('() ~ SetFrag p,FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p)) => TIP (p :+ a) f -> (TIP p f,f a)
prj = undefined {- \case
  MkNil -> error "prj: unreachable case but plugin doesn't find contradiction"   -- TODO how is pattern not a type error?
  MkCons MkFragRep tip x -> case narrowFragRep old MkFragRep of
    Left refl -> here $ co x refl
    Right new -> inner $ MkTIS new x
-}

boxP :: f a -> TIP ('Nil :+ a) f
boxP = ext nil

{-unboxP :: TIP ('Nil :+ a) f -> f a
unboxP = \case
  MkCons MkFragRep MkNil x -> x
  -- MkCons MkFragRep (MkCons MkFragRep _ _) _ -> undefined
  -- MkNil -> undefined
  _ -> error "unboxP pattern is type error, but GHC does not consider it unreachable :("
-}
-----

data F a = MkF{getF :: a}
  deriving (Show)

ex1 :: _
ex1 = boxS $ MkF False

ex2 :: TIS ('Nil :+ Char :+ Bool) F
ex2 = inj $ MkF True

ex3 :: TIS ('Nil :+ Bool :+ Char) F
ex3 = inj $ MkF 'a'

ex4 :: _ => _
ex4 = boxS (MkF 'c') `emb` Proxy @Bool

test1 :: Show a => Maybe (F a) -> IO ()
test1 = print . fmap getF

main :: IO ()
main = do
  let
    exs = [ex1 `emb` Proxy @Char,ex2,ex3,ex4]
  putStrLn "--- Abelian"
  print $ length exs
  putStrLn "--- Inference"
  print $ getF (unboxS ex1)
  test1 $ toMaybe ex1
  putStrLn "--- toMaybe Bool"
  mapM_ (test1 @Bool . toMaybe) exs
  putStrLn "--- toMaybe Char"
  mapM_ (test1 @Char . toMaybe) exs
  putStrLn "--- Case"
  flip mapM_ exs $ absurd "top" `alt` (print @Bool . getF) `alt` (print @Char . getF)
