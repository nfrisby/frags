{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall -Werror #-}
{-# OPTIONS_GHC -Wwarn=partial-type-signatures #-}

{-# OPTIONS_GHC -dcore-lint #-}
{-# OPTIONS_GHC -fplugin=Data.Frag.Plugin #-}
-- {-# OPTIONS_GHC -fplugin-opt Data.Frag.Plugin:trace #-}

{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}

-- {-# OPTIONS_GHC -fprint-explicit-kinds #-}
-- {-# OPTIONS_GHC -dppr-debug -dsuppress-all #-}
-- {-# OPTIONS_GHC -ddump-tc-trace #-}

module Dev where

import Data.Constraint (Constraint)
import Data.Functor.Classes (Show1,showsPrec1)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Contravariant (Op(..))
import Data.Functor.Identity (Identity(..))
import Data.Functor.Product (Product(..))
import Data.Frag
import Data.Proxy (Proxy(..))
import Data.Type.Equality ((:~:)(..))

import Unsafe.Coerce (unsafeCoerce)

data TIS :: Frag k -> (k -> *) -> * where
  MkTIS :: !(FragRep p a) -> f a -> TIS p f

inj :: (FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p)) => f a -> TIS (p :+ a) f
inj = MkTIS MkFragRep

maybeS :: ('() ~ SetFrag p,FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p)) => TIS (p :+ a) f -> Maybe (f a)
maybeS = const Nothing `alt` Just

-- | Add tally.
plusS :: ('() ~ SetFrag p,FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p)) => TIS p f -> proxy a -> TIS (p :+ a) f
plusS = \(MkTIS old x) _ -> MkTIS (widenFragRep old MkFragRep) x

-- | Consume @0@
absurd :: String -> TIS 'Nil f -> a
absurd = \s _ -> error $ "absurd TIS: " ++ s

-- | Remove tally.
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

mapS :: (forall a. f a -> g a) -> TIS fr f -> TIS fr g
mapS = \f (MkTIS rep x) -> MkTIS rep (f x)

elimS :: TIP fr (Compose (Op z) f) -> TIS fr f -> z
elimS = \tos (MkTIS MkFragRep x) -> case setTIP tos of Refl -> getCompose (prj tos) `getOp` x

-----

data TIP :: Frag k -> (k -> *) -> * where
  MkCons :: (FragLT a p ~ 'Nil,FragEQ a p ~ 'Nil) => !(TIP p f) -> f a -> TIP (p :+ a) f
  MkNil :: TIP 'Nil f

setTIP :: TIP fr f -> SetFrag fr :~: '()
setTIP tip = tip `seq` unsafeCoerce Refl   -- simple inductive proof

-- | Build @0@
nil :: TIP 'Nil f
nil = MkNil

-- | Add tally.
ext :: forall a p f. (FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p)) => TIP p f -> f a -> TIP (p :+ a) f
ext = go MkFragRep
  where
  go :: FragRep (q :+ a) a -> TIP q f -> f a -> TIP (q :+ a) f
  go new tip x = case tip of
    MkNil -> MkCons tip x
    MkCons tip' y -> case axiom_minimum new tip' y (setTIP tip') of
      Left Refl -> case new of MkFragRep -> MkCons tip x
      Right (Refl,new',MkApart) -> MkCons (go new' tip' x) y

prj :: (FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p)) => TIP (p :+ a) f -> f a
prj = snd . ret

-- | Remove tally.
ret :: forall a p f. (FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p)) => TIP (p :+ a) f -> (TIP p f,f a)
ret = go (Proxy @p) MkFragRep
  where
  go :: forall q proxy. proxy q -> FragRep (q :+ a) a -> TIP (q :+ a) f -> (TIP q f,f a)
  go q frep@MkFragRep tip = case tip of
--    MkNil -> error "prj pattern is type error, but GHC does not consider it unreachable :("
    MkCons tip' x -> case axiom_minimum2 q (setTIP tip) frep x of
      Left Refl -> (tip',x)
      Right (frep_down,still_min) -> let
        (inner,fa) = go (proxy2 q x) frep_down tip'
        in
        (case (setTIP inner,still_min) of (Refl,Refl) -> inner `ext` x,fa)
    _ -> error "prj pattern is type error, but GHC does not consider it unreachable :("

proxy2 :: proxyp p -> proxya a -> Proxy (q :- a)
proxy2 _ _ = Proxy

boxP :: f a -> TIP ('Nil :+ a) f
boxP = ext nil

unboxP :: TIP ('Nil :+ a) f -> f a
unboxP = \case
  MkCons MkNil x -> x
  -- MkCons MkFragRep (MkCons MkFragRep _ _) _ -> undefined
  -- MkNil -> undefined
  _ -> error "unboxP pattern is type error, but GHC does not consider it unreachable :("

mapP :: (forall a. f a -> g a) -> TIP fr f -> TIP fr g
mapP f = \case
  MkNil -> MkNil
  MkCons tip fa -> MkCons (mapP f tip) (f fa)

foldMapP :: Monoid m => (forall a. f a -> m) -> TIP fr f -> m
foldMapP f = \case
  MkNil -> mempty
  MkCons tip fa -> f fa <> foldMapP f tip

zipWithP :: (forall a. f a -> g a -> h a) -> TIP fr f -> TIP fr g -> TIP fr h
zipWithP _ MkNil MkNil = MkNil
zipWithP f l@(MkCons ltip lx) (MkCons rtip rx) =
  case axiom_minimum3 (mkProxy l) lx rx of
    Refl -> MkCons (zipWithP f ltip rtip) (f lx rx)
  where
  mkProxy :: proxy fr f -> Proxy fr
  mkProxy = \_ -> Proxy
zipWithP _ _ _ = error "foldZipWithP pattern is type error, but GHC does not consider it unreachable :("

-- | @zipP = 'zipWithP' 'Pair'@
zipP :: TIP fr f -> TIP fr g -> TIP fr (Product f g)
zipP = zipWithP Pair

-- | @foldZipWithP f ls rs = 'foldMap' (\('Pair' l r) -> f l r) $ 'zipP' ls rs@
foldZipWithP :: Monoid m => (forall a. f a -> g a -> m) -> TIP fr f -> TIP fr g -> m
foldZipWithP _ MkNil MkNil = mempty
foldZipWithP f l@(MkCons ltip lx) (MkCons rtip rx) =
  case axiom_minimum3 (mkProxy l) lx rx of
    Refl -> f lx rx <> foldZipWithP f ltip rtip
  where
  mkProxy :: proxy fr f -> Proxy fr
  mkProxy = \_ -> Proxy
foldZipWithP _ _ _ = error "foldZipWithP pattern is type error, but GHC does not consider it unreachable :("

data Dict1 pred a = pred a => Dict1

class AllP (pred :: k -> Constraint) (p :: Frag k) where dictP :: TIP p (Dict1 pred)

class AllP_ (pred :: k -> Constraint) (p :: MaybeFragPop k) where
  dictP_ :: Proxy p -> TIP (FragPush p) (Dict1 pred)

instance AllP_ pred (FragPop_NonDet fr) => AllP pred fr where
  dictP = dictP_ (Proxy :: Proxy (FragPop_NonDet fr))

instance AllP_ pred 'NothingFragPop where
  dictP_ _ = nil
instance (KnownFragCard (FragLT b p),FragEQ b p ~ 'Nil,AllP pred p,count ~ ('Nil :+ '()),pred b) => AllP_ pred ('JustFragPop p b count) where
  dictP_ _ = let
    tip :: TIP p (Dict1 pred)
    tip = dictP
    in
    case setTIP tip of Refl -> tip `ext` (Dict1 :: Dict1 pred b)

-----

instance (AllP Show fr,Show1 f) => Show (TIS fr f) where
  showsPrec = \_p tis@(MkTIS frep _) ->
      showChar '<' . showsPrec 0 (fragRepZ frep) . showChar ' '
    .
      (mapP f dictP `elimS` tis)
    .
      showChar '>'
    where
    f :: Dict1 Show a -> Compose (Op ShowS) f a
    f Dict1 = Compose $ Op $ showsPrec1 0

instance (AllP Show fr,Show1 f) => Show (TIP fr f) where
  showsPrec = \_p tip ->
      showChar '{'
    .
      unShowField (foldZipWithP f dictP tip)
    .
      showChar '}'
    where
    f :: Dict1 Show a -> f a -> ShowField
    f = \Dict1 fa -> let g = showsPrec1 11 fa in MkShowField g (showChar ' ' . g)

data ShowField = MkShowField ShowS !ShowS

unShowField :: ShowField -> ShowS
unShowField = \(MkShowField f _) -> f

instance Monoid ShowField where
  mempty = MkShowField id id
instance Semigroup ShowField where
  MkShowField a1 b1 <> MkShowField _ b2 = MkShowField (a1 . b2) (b1 . b2)

-----

ex1 :: _
ex1 = boxS $ Identity False

ex2 :: TIS ('Nil :+ Char :+ Bool) Identity
ex2 = inj $ Identity True

ex3 :: TIS ('Nil :+ Bool :+ Char) Identity
ex3 = inj $ Identity 'a'

ex4 :: _ => _
ex4 = boxS (Identity 'c') `plusS` Proxy @Bool

test1 :: Show a => Maybe (Identity a) -> IO ()
test1 = mapM_ test2

test2 :: Show a => Identity a -> IO ()
test2 = print . runIdentity

ex5 :: _
ex5 = nil `ext` Identity True `ext` Identity 'z' `ext` Identity (3 :: Int)

ex6 :: _
ex6 = nil `ext` Identity True `ext` Identity 'z'

main :: IO ()
main = do
  let
    exs = [ex1 `plusS` Proxy @Char,ex2,ex3,ex4]
  putStrLn "--- TISs"
  print exs
  putStrLn "--- TIPs"
  print ex5
  print ex6

  putStrLn "--- Inference"
  print $ runIdentity (unboxS ex1)
  test1 $ maybeS ex1

  putStrLn "--- maybeS Bool"
  mapM_ (test1 @Bool . maybeS) exs
  putStrLn "--- maybeS Char"
  mapM_ (test1 @Char . maybeS) exs

  putStrLn "--- TIS absurd and alternative"
  flip mapM_ exs $ absurd "top" `alt` (print @Bool . runIdentity) `alt` (print @Char . runIdentity)

  putStrLn "--- TIP projection"
  test2 @Bool $ prj ex5
  test2 @Char $ prj ex5
  test2 @Int $ prj ex5

  putStrLn "--- TIP retraction"
  let
    (r1,x1) = ret ex5
    (r2,x2) = ret r1
    (r3,x3) = ret r2
    _ascribe = r3 `asTypeOf` nil
  test2 @Bool x1
  test2 @Char x2
  test2 @Int x3

  putStrLn "--- elimS"
  let
    mk f = Compose $ Op $ f . runIdentity
    prints = nil `ext` mk (print @Bool) `ext` mk (print @Char)
  prints `elimS` ex4

  putStrLn "--- dictP"
  let
    printD :: Dict1 Show a -> Compose (Op (IO ())) Identity a
    printD = \Dict1 -> mk print
  mapP printD dictP `elimS` ex4
