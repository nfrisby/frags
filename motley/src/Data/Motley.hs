{-# LANGUAGE ConstraintKinds #-}   -- ImplicProd
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
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

{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}

-- {-# OPTIONS_GHC -fplugin-opt Data.Frag.Plugin:trace #-}
-- {-# OPTIONS_GHC -fprint-explicit-kinds #-}
-- {-# OPTIONS_GHC -dppr-debug -dsuppress-all #-}
-- {-# OPTIONS_GHC -ddump-tc-trace #-}

module Data.Motley (
  -- * Products
  Prod(..),
  ext,
  prj,
  nil,
  ret,
  -- ** Evidence
  polyProd,
  proofProd,
  -- ** Zip
  foldZipWithProd,
  zipProd,
  zipWithProd,
  sameSum,
  -- * Sums
  Sum(..),
  absurd,
  alt,
  inj,
  -- * Operators
  foldMapProd,
  foldMapSum,
  fragRepProd,
  fragRepSum,
  fromSingletonProd,
  fromSingletonSum,
  idProd,
  idSum,
  mapProd,
  mapSum,
  opticProd,
  opticProd',
  opticSum,
  opticSum',
  toSingletonProd,
  toSingletonSum,
  traverseProd,
  traverseSum,
  updateProd,
  updateSum,
  -- ** Eliminators
  elimProd,
  elimProdSum,
  elimSum,
  elimSumProd,
  -- ** Pedantry
  introProd,
  introSum,
  minusProd,
  minusSum,
  plusProd,
  plusSum,
  zeroProd,
  zeroSum,
  -- * Re-exports
  -- ** From "Data.Frag"
  type (:-), type (:+), Frag(Nil), FragEQ, FragLT, KnownFragCard, SetFrag,
  -- ** Useful functors
  At(..),
  Compose(..),
  Const(..),
  Identity(..),
  Op(..),
  Product(..),
  Proxy(..),
  U1(..),
  -- ** Implicit values
  Dict1(..),
  Implic(..),
  -- * Miscellany
  ImplicProd,
  implicProd,
  ) where

import qualified Control.Lens as Lens
import qualified Control.Lens.Iso as Iso
import qualified Control.Lens.Prism as Prism
import qualified Data.Functor.Arity1ToHask.Classes as A1H
import Data.Functor.At (At(..))
import Data.Functor.Compose (Compose(..))
import Data.Functor.Const (Const(..))
import Data.Functor.Contravariant (Op(..))
import Data.Functor.Product (Product(..))
import Data.Functor.Identity (Identity(..))
import Data.Functor.Fun (type (~>)(..))
import Data.Frag
import Data.Implic (Dict1(..),Dict2(..),Implic(..))
import qualified Data.Monoid as M
import Data.Proxy (Proxy(..))
import Data.Type.Equality ((:~:)(..),testEquality)
import GHC.Generics (U1(..))
import qualified Test.QuickCheck as QC

import Unsafe.Coerce (unsafeCoerce)

asc1 :: f a -> g a -> f a
asc1 = const

-----

data Sum :: Frag k -> (k -> *) -> * where
  MkSum :: !(FragRep p a) -> f a -> Sum p f

-- | Alias of 'absurd'
zeroSum :: Sum 'Nil f -> a
zeroSum = absurd "zeroSum"

inj :: (FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p)) => f a -> Sum (p :+ a) f
inj = MkSum MkFragRep

class    (FragEQ a p ~ ('Nil :+ '()),KnownFragCard (FragLT a p)) => ToMaybeConSum p a
instance (FragEQ a p ~ ('Nil :+ '()),KnownFragCard (FragLT a p)) => ToMaybeConSum p a
instance SetFrag p ~ '() => A1H.ToMaybe (Sum p) where
  type ToMaybeCon (Sum p) = ToMaybeConSum p
  toMaybe = const Nothing `alt` Just

-- |
plusSum :: ('() ~ SetFrag p,FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p)) => Sum p f -> proxy a -> Sum (p :+ a) f
plusSum = \(MkSum old x) _ -> MkSum (widenFragRep old MkFragRep) x

-- | Consume @0@
absurd :: String -> Sum 'Nil f -> a
absurd = \s _ -> error $ "absurd Sum: " ++ s

-- | Alias of 'alt'
minusSum :: ('() ~ SetFrag p,FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p)) => (Sum p f -> ans) -> (f a -> ans) -> Sum (p :+ a) f -> ans
minusSum = alt

-- | Remove a tally
alt ::
    ('() ~ SetFrag p,FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p))
  =>
    (Sum p f -> ans) -> (f a -> ans) -> Sum (p :+ a) f -> ans
alt = \inner here (MkSum old x) -> case narrowFragRep old MkFragRep of
  Left refl -> here $ co x refl
  Right new -> inner $ MkSum new x
  where
  co :: f a -> a :~: b -> f b
  co x Refl = x

opticSum' ::
    (SetFrag p ~ '(),FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p))
  =>
    Prism.Prism' (Sum (p :+ a) f) (f a)
opticSum' = opticSum

opticSum ::
    (SetFrag p ~ '(),FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p),FragEQ b p ~ 'Nil,KnownFragCard (FragLT b p))
  =>
    Prism.Prism (Sum (p :+ a) f) (Sum (p :+ b) f) (f a) (f b)
opticSum = \f -> let
  step1 = alt Left Right
  step2 = Prism.right' f
  step3 = \case
    Left miss -> pure $ miss `plusSum` Proxy
    Right hit -> inj <$> hit
  in Iso.dimap step1 step3 step2

toSingletonSum :: f a -> Sum ('Nil :+ a) f
toSingletonSum = inj

fromSingletonSum :: Sum ('Nil :+ a) f -> f a
fromSingletonSum = \(MkSum MkFragRep x) -> x

mapSum :: (forall a. f a -> g a) -> Sum fr f -> Sum fr g
mapSum = \f (MkSum rep x) -> MkSum rep (f x)

instance A1H.Functor (Sum fr) where fmap = mapSum
instance A1H.Foldable (Sum fr) where foldMap = foldMapSum
instance A1H.Traversable (Sum fr) where traverse = traverseSum

type family FromJustFragPop (just :: MaybeFragPop k) :: k where
  FromJustFragPop ('JustFragPop p a count) = a

instance (fr ~ ('Nil :+ a)) => A1H.Singleton (Sum fr) where
  type Point (Sum fr) = FromJustFragPop (FragPop_NonDet fr)
  singletonIso = Iso.iso toSingletonSum fromSingletonSum

foldMapSum :: Monoid m => (forall a. f a -> m) -> Sum fr f -> m
foldMapSum = \f (MkSum _ x) -> f x

traverseSum :: Applicative af => (forall a. f a -> af (g a)) -> Sum fr f -> af (Sum fr g)
traverseSum = \f (MkSum frep x) -> MkSum frep <$> f x

fragRepSum :: Sum p f -> Sum p (Product (FragRep p) f)
fragRepSum = \(MkSum frep x) -> MkSum frep (Pair frep x)

sameSum :: (SetFrag p ~ '()) => Sum p f -> Sum p g -> Maybe (Sum p (Product f g))
sameSum (MkSum frep1 x1) (MkSum frep2 x2) = case testEquality frep1 frep2 of
  Just Refl -> Just $ MkSum frep1 (Pair x1 x2)
  Nothing -> Nothing

-----

data Prod :: Frag k -> (k -> *) -> * where
  MkCons :: (FragLT a p ~ 'Nil,FragEQ a p ~ 'Nil) => !(Prod p f) -> f a -> Prod (p :+ a) f
  MkNil :: Prod 'Nil f

proofProd :: Prod fr f -> SetFrag fr :~: '()
proofProd tip = tip `seq` unsafeCoerce Refl   -- simple inductive proof

-- | Build @0@
nil :: Prod 'Nil f
nil = MkNil

-- | Alias of 'nil'
zeroProd :: Prod 'Nil f
zeroProd = nil

-- | Alias of 'ext'
plusProd :: (FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p)) => Prod p f -> f a -> Prod (p :+ a) f
plusProd = ext

-- | Alias of 'ret'
minusProd :: (FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p)) => Prod (p :+ a) f -> (Prod p f,f a)
minusProd = ret

infixl 8 `ext`

-- | Add a tally
ext :: forall a p f. (FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p)) => Prod p f -> f a -> Prod (p :+ a) f
ext = go MkFragRep
  where
  go :: FragRep (q :+ a) a -> Prod q f -> f a -> Prod (q :+ a) f
  go new tip x = case tip of
    MkNil -> MkCons tip x
    MkCons tip' y -> case axiom_minimum new tip' y (proofProd tip') of
      Left Refl -> case new of MkFragRep -> MkCons tip x
      Right (Refl,new',MkApart) -> MkCons (go new' tip' x) y

opticProd ::
    (FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p),FragEQ b p ~ 'Nil,KnownFragCard (FragLT b p))
  =>
    Lens.Lens (Prod (p :+ a) f) (Prod (p :+ b) f) (f a) (f b)
opticProd = \f prod -> let
  (prod',x) = ret prod
  in ext prod' <$> f x

opticProd' ::
  forall a p f.
    (FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p))
  =>
    Lens.Lens' (Prod (p :+ a) f) (f a)
opticProd' = go MkFragRep
  where
  go :: forall q g. Functor g => FragRep q a -> (f a -> g (f a)) -> Prod q f -> g (Prod q f)
  go frep f tip = case tip of
    MkCons tip' x -> case narrowFragRepD (proofProd tip') frep (MkFragRep `asc1` x) of
      Left Refl -> case frep of MkFragRep -> MkCons tip' <$> f x
      Right frep' -> flip MkCons x <$> go frep' f tip'
    _ -> error "https://gitlab.haskell.org/ghc/ghc/issues/16639"

prj :: (FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p)) => Prod (p :+ a) f -> f a
prj = snd . ret

class    (FragEQ a p ~ ('Nil :+ '()),KnownFragCard (FragLT a p)) => ToMaybeConProd p a
instance (FragEQ a p ~ ('Nil :+ '()),KnownFragCard (FragLT a p)) => ToMaybeConProd p a
instance SetFrag p ~ '() => A1H.ToMaybe (Prod p) where
  type ToMaybeCon (Prod p) = ToMaybeConProd p
  toMaybe = Just . prj

-- | Remove a tally
ret :: forall a p f. (FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p)) => Prod (p :+ a) f -> (Prod p f,f a)
ret = go (Proxy @p) MkFragRep
  where
  go :: forall q proxy. proxy q -> FragRep (q :+ a) a -> Prod (q :+ a) f -> (Prod q f,f a)
  go q frep@MkFragRep tip = case tip of
    MkCons tip' x -> case axiom_minimum2 q (proofProd tip) frep x of
      Left Refl -> (tip',x)
      Right (frep_down,still_min) -> let
        (inner,fa) = go (proxy2 q x) frep_down tip'
        in
        (case (proofProd inner,still_min) of (Refl,Refl) -> inner `ext` x,fa)
    _ -> error "https://gitlab.haskell.org/ghc/ghc/issues/16639"

fragRepProd :: forall p f. Prod p f -> Prod p (Product (FragRep p) f)
fragRepProd = go id
  where
  go :: (forall a. FragRep q a -> FragRep p a) -> Prod q f -> Prod q (Product (FragRep p) f)
  go = \f -> \case
    MkCons tip x -> let
      frep = MkFragRep
      in
      MkCons (go (\frep' -> f (widenFragRepByMin frep frep')) tip) (Pair (f frep) x)
    MkNil -> MkNil

proxy2 :: proxyp p -> proxya a -> Proxy (q :- a)
proxy2 _ _ = Proxy

toSingletonProd :: f a -> Prod ('Nil :+ a) f
toSingletonProd = ext nil

fromSingletonProd :: Prod ('Nil :+ a) f -> f a
fromSingletonProd = \case
  MkCons MkNil x -> x
  _ -> error "https://gitlab.haskell.org/ghc/ghc/issues/16639"

mapProd :: (forall a. f a -> g a) -> Prod fr f -> Prod fr g
mapProd f = \case
  MkNil -> MkNil
  MkCons tip fa -> MkCons (mapProd f tip) (f fa)

traverseProd :: Applicative af => (forall a. f a -> af (g a)) -> Prod fr f -> af (Prod fr g)
traverseProd f = \case
  MkNil -> pure MkNil
  MkCons tip fa -> MkCons <$> traverseProd f tip <*> f fa

instance A1H.Functor (Prod fr) where fmap = mapProd
instance A1H.Foldable (Prod fr) where foldMap = foldMapProd
instance A1H.Traversable (Prod fr) where traverse = traverseProd

instance (fr ~ ('Nil :+ a)) => A1H.Singleton (Prod fr) where
  type Point (Prod fr) = FromJustFragPop (FragPop_NonDet fr)
  singletonIso = Iso.iso toSingletonProd fromSingletonProd

foldMapProd :: Monoid m => (forall a. f a -> m) -> Prod fr f -> m
foldMapProd f = \case
  MkNil -> mempty
  MkCons tip fa -> f fa <> foldMapProd f tip

zipWithProd :: (forall a. f a -> g a -> h a) -> Prod fr f -> Prod fr g -> Prod fr h
zipWithProd _ MkNil MkNil = MkNil
zipWithProd f l@(MkCons ltip lx) (MkCons rtip rx) =
  case axiom_minimum3 (mkProxy l) lx rx of
    Refl -> MkCons (zipWithProd f ltip rtip) (f lx rx)
  where
  mkProxy :: proxy fr f -> Proxy fr
  mkProxy = \_ -> Proxy
zipWithProd _ _ _ = error "https://gitlab.haskell.org/ghc/ghc/issues/16639"

instance Implic (Prod fr U1) => A1H.Applicative (Prod fr) where
  pure = polyProd
  liftA2 = zipWithProd

polyProd :: Implic (Prod fr U1) => (forall a. f a) -> Prod fr f
polyProd = \f -> g f `A1H.fmap` implic
  where
  g :: (forall b. f b) -> U1 a -> f a
  g = \f U1 -> f

-- | Abbreviation of @'zipWithP' 'Pair'@
zipProd :: Prod fr f -> Prod fr g -> Prod fr (Product f g)
zipProd = zipWithProd Pair

-- | Abbreviation of @\\f ls rs -> 'foldMapProd' (\\('Pair' l r) -> f l r) $ 'zipProd' ls rs@
foldZipWithProd :: Monoid m => (forall a. f a -> g a -> m) -> Prod fr f -> Prod fr g -> m
foldZipWithProd _ MkNil MkNil = mempty
foldZipWithProd f l@(MkCons ltip lx) (MkCons rtip rx) =
  case axiom_minimum3 (mkProxy l) lx rx of
    Refl -> f lx rx <> foldZipWithProd f ltip rtip
  where
  mkProxy :: proxy fr f -> Proxy fr
  mkProxy = \_ -> Proxy
foldZipWithProd _ _ _ = error "https://gitlab.haskell.org/ghc/ghc/issues/16639"

class ImplicProd_ (f :: k -> *) (p :: MaybeFragPop k) where
  implicProd :: proxy p -> Prod (FragPush p) f

type ImplicProd f fr = ImplicProd_ f (FragPop_NonDet fr)

instance ImplicProd_ f (FragPop_NonDet p) => Implic (Prod p f) where
  implic = implicProd (Proxy :: Proxy (FragPop_NonDet p))

instance ImplicProd_ f 'NothingFragPop where
  implicProd = \_ -> nil
instance (KnownFragCard (FragLT b p),FragEQ b p ~ 'Nil,Implic (Prod p f),count ~ ('Nil :+ '()),Implic (f b)) => ImplicProd_ f ('JustFragPop p b count) where
  implicProd = \_ -> let
    tip :: Prod p f
    tip = implic
    in
    case proofProd tip of Refl -> tip `ext` (implic :: f b)

-----

instance Implic (Prod fr (Compose (Dict1 Eq) f)) => Eq (Sum fr f) where
  c1 == c2 = case proofProd dicts of
    Refl -> case sameSum c1 c2 of
      Just (MkSum MkFragRep (Pair x1 x2)) -> f (prj dicts) x1 x2
      Nothing -> False
    where
    dicts :: Prod fr (Compose (Dict1 Eq) f)
    dicts = implic

    f :: Compose (Dict1 Eq) f a -> f a -> f a -> Bool
    f (Compose MkDict1) = (==)

instance Implic (Prod fr (Compose (Dict1 Show) f)) => Show (Sum fr f) where
  showsPrec = \_p tis@(MkSum frep _) ->
      showChar '<' . showsPrec 0 (fragRepZ frep) . showChar ' '
    .
      (mapProd f implic `elimProdSum` tis)
    .
      showChar '>'
    where
    f :: Compose (Dict1 Show) f a -> Compose (Op ShowS) f a
    f (Compose MkDict1) = Compose $ Op $ showsPrec 0

instance Implic (Prod fr (Compose (Dict1 Eq) f)) => Eq (Prod fr f) where
  (==) = \l r -> M.getAll $ foldZipWithProd f implic (zipProd l r)
    where
    f :: Compose (Dict1 Eq) f a -> Product f f a -> M.All
    f = \(Compose MkDict1) (Pair l r) -> M.All $ l == r

instance Implic (Prod fr (Compose (Dict1 Show) f)) => Show (Prod fr f) where
  showsPrec = \_p tip ->
      showChar '{'
    .
      unShowField (foldZipWithProd f implic tip)
    .
      showChar '}'
    where
    f :: Compose (Dict1 Show) f a -> f a -> ShowField
    f = \(Compose MkDict1) fa -> let g = showsPrec 11 fa in MkShowField g (showChar ' ' . g)

data ShowField = MkShowField ShowS !ShowS

unShowField :: ShowField -> ShowS
unShowField = \(MkShowField f _) -> f

instance Monoid ShowField where
  mempty = MkShowField id id
instance Semigroup ShowField where
  MkShowField a1 b1 <> MkShowField _ b2 = MkShowField (a1 . b2) (b1 . b2)

-----

elimProdSum :: Prod fr (Compose (Op z) f) -> Sum fr f -> z
elimProdSum = \tos (MkSum MkFragRep x) -> case proofProd tos of
  Refl -> getCompose (prj tos) `getOp` x

elimSumProd :: Sum fr (Compose (Op z) f) -> Prod fr f -> z
elimSumProd = \(MkSum MkFragRep x) tos -> case proofProd tos of
  Refl -> getCompose x `getOp` (prj tos)

elimProd :: Monoid m => Prod fr (Const m) -> m
elimProd = foldMapProd getConst

elimSum :: Sum ('Nil :+ a) f -> f a
elimSum = fromSingletonSum

introProd :: Prod p (Compose ((->) a) f) -> a -> Prod p f
introProd = \fs a -> A1H.fmap (\(Compose f) -> f a) fs

introSum :: Sum p (Compose ((->) a) f) -> a -> Sum p f
introSum = \(MkSum MkFragRep f) a -> MkSum MkFragRep (getCompose f a)

updateSum :: Prod p (f ~> g) -> Sum p f -> Sum p g
updateSum = \fs (MkSum frep@MkFragRep x) -> MkSum frep $ prj fs `appFun` x

updateProd :: Sum p (Compose M.Endo f) -> Prod p f -> Prod p f
updateProd = \(MkSum MkFragRep (Compose (M.Endo fun))) -> Lens.over opticProd' fun

-----

idProd :: Prod p f -> Prod p f
idProd = id

idSum :: Sum p f -> Sum p f
idSum = id

-----

class    QC.Arbitrary (f a) => ArbitraryF f a
instance QC.Arbitrary (f a) => ArbitraryF f a

-- | Generates each factor under @'QC.scale' (\sz -> div sz n)@
instance Implic (Prod p (Dict2 ArbitraryF f)) => QC.Arbitrary (Prod p f) where
  arbitrary = let
    arbs :: Prod p (Dict2 ArbitraryF f)
    arbs = implic

    len = M.getSum $ foldMapProd (\_ -> M.Sum (1 :: Int)) arbs

    f :: Dict2 ArbitraryF f a -> QC.Gen (f a)
    f = \MkDict2 -> QC.scale (`div` len) $ QC.arbitrary
    in
    traverseProd f implic

  shrink = \tip -> let
    f :: forall a. Product (FragRep p) (Dict2 ArbitraryF f) a -> [[Prod p f]]
    f = \(Pair MkFragRep MkDict2) -> [opticProd' (\x -> QC.shrink (x :: f a)) tip]

    interleave [] [] = []
    interleave acc [] = interleave [] acc
    interleave acc ([]:xss) = interleave acc xss
    interleave acc ((x:xs):xss) = x : interleave (xs : acc) xss
    in
    interleave [] $ foldMapProd f (fragRepProd implic)

-- | Does not adjust size
instance Implic (Prod p (Dict2 ArbitraryF f)) => QC.Arbitrary (Sum p f) where
  arbitrary = let
    f :: Product (FragRep p) (Dict2 ArbitraryF f) a -> [QC.Gen (Sum p f)]
    f = \(Pair frep MkDict2) -> [MkSum frep <$> QC.arbitrary]
    in
    QC.oneof $ foldMapProd f (fragRepProd implic)

  shrink = let
    f :: Dict2 ArbitraryF f a -> (f ~> Compose [] f) a
    f = \MkDict2 -> MkFun (Compose . QC.shrink)

    shrinks :: Prod p (f ~> Compose [] f)
    shrinks = mapProd f implic
    in
    traverseSum getCompose . updateSum shrinks
