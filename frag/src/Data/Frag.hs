{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}   -- /~
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- | Type-level multisets with an interface restricted to that of traditional row-types.
--
-- You almost always need to use
--
-- > {-# OPTIONS_GHC -dcore-lint -fplugin=Data.Frag.Plugin #-}
--
-- when importing this module.

module Data.Frag (
  -- * Frag Signature
  Frag(Nil),
  type (:+),
  type (:-),

  -- * Frag Families
  FragCard,
  FragEQ,
  FragLT,
  FragNE,

  -- * Frag Decomposition
  MaybeFragPop(..),
  FragPop_NonDet,
  FragPush,

  -- * Frag Evidence
  EqFrag,
  KnownFragCard,
  SetFrag,
  fragCard,
  fragCard',

  -- * Stable Type Ordering
  Ordered(..),
  swapOrdered,
  -- ** Strict
  (:<:)(..),
  axiom_lessThan_apart,
  axiom_lessThan_antisym,
  axiom_lessThan_irrefl,
  axiom_lessThan_trans,
  axiom_lessThan_total,
  axiom_FragLT_plus_greater,
  unsafeLessThan,
  -- ** Minima
  axiom_FragLT0,
  axiom_FragLT0_apart,
  axiom_FragLT0_trans,
  axiom_minimum_unique,
  test_FragLT0,

  -- * Row Types
  DomFrag,
  Mapping(..),
  MappingArg,
  MappingVal,
  (:=),

  -- * Miscellany
  type (/~),
  (:/~:)(..),
  Apart,
  ApartPairs(ConsApart,OneApart),
  ProxyInt,
  axiom_apart_irrefl,
  axiom_apart_multiplicity01,
  unsafeMkApart,
  unsafeProxyInt,
  unsafeConvertProxyInt,
  ) where

import Data.Functor.Identity (runIdentity)
import Data.Proxy (Proxy(..))
import Data.Type.Equality
import GHC.Exts (Int(I#),Int#,Proxy#,proxy#)
import Unsafe.Coerce (unsafeCoerce)

-- | A type-level signed multiset over @k@, /i.e./ an element of a FRee Abelian Group with basis @k@.
--
-- <https://ncatlab.org/nlab/show/free+abelian+group>
--
-- Note that @Frag ()@ is isomorphic to the integers.
--
-- This module adopts the additive flavor for the group signature,
-- and furthermore restricts it to the signed unary/Peano representation of 'Nil', ':+', and ':-'.
data Frag (k :: *) =
    Nil

-- | Increment this basis element's multiplicity.
type family (:+) (fr :: Frag k) (e :: k) :: Frag k where {}
infixl 6 :+

-- | Decrement this basis element's multiplicity.
type family (:-) (fr :: Frag k) (e :: k) :: Frag k where {}
infixl 6 :-

-----

-- | Combined multiplicity of all basis elements.
type family FragCard (fr :: Frag k) :: Frag () where
  FragCard 'Nil = 'Nil

-- | Combined multiplicity of the basis elements equivalent to this one.
type family FragEQ (a :: k) (fr :: Frag k) :: Frag () where
  FragEQ k 'Nil = 'Nil

-- | Combined multiplicity of basis elements less than this one in GHC's arbitrary type ordering.
type family FragLT (a :: k) (fr :: Frag k) :: Frag () where
  FragLT k 'Nil = 'Nil

-- | Basis elements not equivalent to this one.
type family FragNE (a :: k) (fr :: Frag k) :: Frag k where
  FragNE k 'Nil = 'Nil

-----

-- | Implementation detail
newtype ProxyInt (fr :: Frag k) = MkProxyInt Int

-- | Implementation detail
unsafeProxyInt :: forall k. ProxyInt ('Nil :: Frag k)
{-# INLINE unsafeProxyInt #-}
unsafeProxyInt = MkProxyInt 0

-- | Implementation detail
unsafeConvertProxyInt :: forall k fr1 fr2. ProxyInt (fr1 :: Frag k) -> Int# -> ProxyInt (fr2 :: Frag k)
{-# INLINE unsafeConvertProxyInt #-}
unsafeConvertProxyInt (MkProxyInt x) i = MkProxyInt (x + I# i)

-- | Compare to 'KnownNat'.
class KnownFragCard (fr :: Frag k) where method_KnownFragCard :: ProxyInt fr

instance KnownFragCard 'Nil where method_KnownFragCard = MkProxyInt 0

-- | 'fragCard' is the cardinality of the frag.
fragCard :: forall fr proxy. KnownFragCard fr => proxy fr -> Int
fragCard = \_ -> fragCard' (proxy# :: Proxy# fr)

-- | See 'fragCard'.
fragCard' :: forall fr. KnownFragCard fr => Proxy# fr -> Int
fragCard' = \_ -> let MkProxyInt i = method_KnownFragCard :: ProxyInt fr in i

-- | Each multiplicity is either 0 or 1.
--
-- This is intuitively a class @SetFrag :: Frag k -> Constraint@.
-- But because it can imply type equivalence constraints,
-- we phrase the predicate as a trivial type family equivalence,
-- so that GHC will not float equivalence constraints out from under it.
type family SetFrag (fr :: Frag k) :: () where
  SetFrag 'Nil = '()

-----

-- | Evidence that @a < b@ in GHC's arbitrary type ordering.
data (:<:) :: k -> k -> * where
  LessThan :: (a /~ b,FragLT b ('Nil :+ a) ~ ('Nil :+ '())) => a :<: b

-- |
unsafeLessThan :: proxya a -> proxyb b -> a :<: b
unsafeLessThan = \_ _ -> let
  res :: forall a b. a :<: b
  res = runIdentity $ do
    Refl <- pure (unsafeRefl Proxy Proxy :: FragLT b ('Nil :+ a) :~: ('Nil :+ '()))
    MkApart <- pure (unsafeMkApart Proxy Proxy :: a :/~: b)
    pure LessThan
  in
  res

-- | \"trichotomous relation\"
axiom_lessThan_apart :: a :<: b -> a :/~: b
axiom_lessThan_apart LessThan = MkApart

-- |
axiom_lessThan_irrefl :: String -> a :<: a -> x
axiom_lessThan_irrefl s !_ = error $ "Data.Frag.abasurd_lessThan " ++ s

-- |
axiom_lessThan_antisym :: String -> b :<: a -> a :<: b -> x
axiom_lessThan_antisym s !_ !_ = error $ "Data.Frag.abasurd_lessThan " ++ s

-- |
axiom_lessThan_trans :: a :<: b -> b :<: c -> a :<: c
axiom_lessThan_trans LessThan LessThan = unsafeLessThan Proxy Proxy

-- | If nothing is less than @z@ in a set @p@, then @z@ is less than every element.
axiom_FragLT0 ::
    proxyp p -> proxyz z -> proxya a
  ->
    SetFrag p :~: '()
  ->
    FragEQ a p :~: ('Nil :+ '())
  ->
    FragLT z p :~: 'Nil
  ->
    a :/~: z
  ->
    z :<: a
axiom_FragLT0 _ z a !_ !_ !_ !_ = unsafeLessThan z a

-- | Removing an element other than one that's less than all the others preserves that property.
axiom_FragLT0_apart ::
    proxyp p -> proxya a -> proxyz z
  ->
    SetFrag (p :+ a) :~: '()
  ->
    a :/~: z
  ->
    FragLT z (p :+ a) :~: 'Nil
  ->
    FragLT z p :~: 'Nil
axiom_FragLT0_apart _ _ _ !_ !_ !_ = unsafeRefl Proxy Proxy

-- | If
--
-- * @p@ is a set
-- * @a@ is in @p@
-- * @b@ is not in @p@
--
-- then the plugin concludes @a /~ b@.
--
-- Thus @a < b@ or @b > a@,
-- and we can determine which by comparing the counts of their lessers.
axiom_lessThan_total ::
    (
      KnownFragCard (FragLT b p)
    ,
      KnownFragCard (FragLT a p)
    )
  =>
    proxyp p -> proxya a -> proxyb b
  ->
    SetFrag p :~: '()   -- TODO use NonNegFrag p once we have it
  ->
    FragEQ a p :~: ('Nil :+ '())
  ->
    FragEQ b p :~: 'Nil
  ->
    Either (a :<: b) (b :<: a)
axiom_lessThan_total
  (_ :: proxyp p) (a :: proxya a) (b :: proxyb b)
  Refl Refl Refl
  =
  if fragCard (Proxy :: Proxy (FragLT a p)) < fragCard (Proxy :: Proxy (FragLT b p))
  then Left $ unsafeLessThan a b
  else Right $ unsafeLessThan b a

-- | 'FragLT' ignores greater elements.
axiom_FragLT_plus_greater ::
    proxyp p -> proxyk k
  ->
    z :<: a
  ->
    FragLT z p :~: k
  ->
    FragLT z (p :+ a) :~: k
axiom_FragLT_plus_greater _ _ !_ !_ = unsafeRefl Proxy Proxy

-- | Anything less than the minimum is also less than every element.
axiom_FragLT0_trans ::
    proxyp p
  ->
    a :<: z
  ->
    FragLT z p :~: 'Nil
  ->
    FragLT a p :~: 'Nil
axiom_FragLT0_trans _ !_ !_ = unsafeRefl Proxy Proxy

-- | The minimum of a set is unique.
axiom_minimum_unique ::
    proxyp p -> proxya a -> proxyb b
  ->
    SetFrag p :~: '()   -- TODO use NonNegFrag p once we have it
  ->
    FragLT a p :~: 'Nil -> FragEQ a p :~: ('Nil :+ '())
  ->
    FragLT b p :~: 'Nil -> FragEQ b p :~: ('Nil :+ '())
  ->
    a :~: b
axiom_minimum_unique _p a b Refl Refl Refl Refl Refl = unsafeRefl a b

-- | Check the multiplicity of all basis elements in @p@ that are less than @a@ add up to zero.
test_FragLT0 ::
    KnownFragCard (FragLT a p)
  =>
    proxyp p -> proxya a -> Maybe (FragLT a p :~: 'Nil)
test_FragLT0 (_ :: proxyp p) (_ :: proxya a) =
  if 0 == fragCard (Proxy :: Proxy (FragLT a p))
  then Just $ unsafeRefl Proxy Proxy
  else Nothing

-- | Evidence relating two types according to GHC's arbitrary type ordering.
data Ordered a b =
    TypeLT (a :<: b)
  |
    TypeEQ (a :~: b)
  |
    TypeGT (b :<: a)

-- |
swapOrdered :: Ordered a b -> Ordered b a
swapOrdered = \case
  TypeLT x -> TypeGT x
  TypeEQ x@Refl -> TypeEQ x
  TypeGT x -> TypeLT x

-----

-- | Apartness constraint; at least one pair is apart.
--
-- <https://ncatlab.org/nlab/show/apartness+relation>
--
-- We could assert apartness of equal-length tuples of types instead of baking in the list of pairs;
-- however, this approach has no arbitrary upper bound on the length, fewer kind arguments, clearer distinction between itself and userland types, etc.
--
-- NOTE: This class is necessary for the program logic involving frags,
-- but its logic does not inherently depend on frags.
-- Unfortunately, neither GHC nor some other plugin currently provides apartness constraints.
type family Apart (pairs :: ApartPairs) :: () where
  Apart ('OneApart 'False 'True) = '()

-- | See 'Apart'.
data ApartPairs =
    forall k.   -- TODO need hetero?
    ConsApart k k ApartPairs
  |
    forall k.   -- TODO need hetero?
    OneApart k k

-- | A proof that two types are apart; analogous to '(:~:).
data (:/~:) a b = (Apart ('OneApart a b) ~ '()) => MkApart

-- |
type (/~) a b = (Apart ('OneApart a b) ~ '())

-----

-- | Ultimately the plugin automate this inference,
-- but it would be costly without knowing which @p@ to use.
--
-- TODO handle apartness at kind @Frag '()@ in plugin,
-- and provide @proxy p -> (FragEQ a p :/~: FragEQ b p) -> a :/~: b@.
axiom_apart_multiplicity01 ::
    (FragEQ a p ~ 'Nil,FragEQ b p ~ ('Nil :+ '()))
  =>
    proxyp p -> proxya a -> proxyb b -> a :/~: b
axiom_apart_multiplicity01 = \_ a b -> unsafeMkApart a b

unsafeRefl :: proxya a -> proxyb -> a :~: b
unsafeRefl = \_ _ -> unsafeCoerce Refl

-- |
unsafeMkApart :: proxya a -> proxyb b -> a :/~: b
unsafeMkApart = \_ _ -> unsafeCoerce (MkApart :: 'False :/~: 'True)

-- |
axiom_apart_irrefl :: String -> a :~: b -> a :/~: b -> x
axiom_apart_irrefl s !_ !_ = error $ "Data.Frag.axiom_eq_apart " ++ s

-----

-- | INVARIANT: Never reduces to @'JustFragPop' _ _ 'Nil@.
--
-- WARNING: This family chooses which basis element to pop in a non-deterministic way.
type family FragPop_NonDet (fr :: Frag k) :: MaybeFragPop k where
  FragPop_NonDet 'Nil = 'NothingFragPop

-- | Inverse of 'FragPop_NonDet'.
type family FragPush (arg :: MaybeFragPop k) :: Frag k where
  FragPush 'NothingFragPop = 'Nil

-- | Codomain of 'FragPop_NonDet'.
data MaybeFragPop k =
    JustFragPop (Frag k) k (Frag ())
  |
    NothingFragPop

-----

-- | An alternative to @~@ at kind @Frag@, useful for technical reasons.
type family EqFrag (l :: Frag k) (r :: Frag k) :: () where
  EqFrag 'Nil 'Nil = '()

-----

infix 7 :=

-- | A pair in a function's graph.
--
-- A frag with basis 'Mapping' is a row type,
-- but the plugin only provides some of the expected theory.
data Mapping dom cod = To dom cod

-- |
type (:=) = 'To

-- | Get first argument of ''To'.
type family MappingArg (mapping :: Mapping dom cod) :: dom where
  MappingArg ('To arg val) = arg

-- | Get second argument of ''To'.
type family MappingVal (mapping :: Mapping dom cod) :: cod where
  MappingVal ('To arg val) = val

-- | Apply 'MappingArg' to every basis element.
type family DomFrag (fr :: Frag (Mapping dom cod)) :: Frag dom where
  DomFrag 'Nil = 'Nil
