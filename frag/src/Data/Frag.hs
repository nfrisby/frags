{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}   -- /~
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

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
  KnownFragCard,
  SetFrag,
  fragCard,
  fragCard',

  -- * Frag-based 'Type.Reflection.Typeable'
  FragRep(..),
  apartByFragEQ01,
  axiom_minimum,
  axiom_minimum2,
  axiom_minimum3,
  fragRepZ,
  narrowFragRep,
  narrowFragRep',
  testFragRepNil,
  widenFragRep,

  -- * Miscellany
  type (/~),
  (:/~:)(..),
  Apart,
  ApartPairs(ConsApart,OneApart),
  ProxyInt,
  unsafeProxyInt,
  unsafeConvertProxyInt,
  ) where

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

-- | Compare to 'Type.Reflection.TypeRep'
data FragRep :: Frag k -> k -> * where
  MkFragRep :: (FragEQ a fr ~ ('Nil :+ '()),KnownFragCard (FragLT a fr)) => FragRep fr a

-- |
fragRepZ :: forall fr a. FragRep fr a -> Int
fragRepZ MkFragRep = fragCard' (proxy# :: Proxy# (FragLT a fr))

instance SetFrag fr ~ '() => TestEquality (FragRep fr) where
  testEquality l r
    | fragRepZ l == fragRepZ r = Just $ unsafeCoerce Refl
    | otherwise = Nothing

-----

-- | Compare to the @Lacks@ axiom from Gaster and Jones.
widenFragRep :: (SetFrag fr ~ '()) => FragRep fr a -> FragRep (fr :+ b) b -> FragRep (fr :+ b) a
{-# INLINE widenFragRep #-}
widenFragRep a@MkFragRep b = unsafeCoerce $
  if fragRepZ a < fragRepZ b then a else shiftFragRep incr a
  where
  incr i = i + 1

-- | Compare to the @Lacks@ axiom from Gaster and Jones.
narrowFragRep :: (SetFrag fr ~ '()) => FragRep (fr :+ b) a -> FragRep (fr :+ b) b -> Either (a :~: b) (FragRep fr a)
{-# INLINE narrowFragRep #-}
narrowFragRep a@MkFragRep b = case fragRepZ a `compare` fragRepZ b of
  EQ -> Left (unsafeCoerce Refl)
  LT -> Right $ unsafeCoerce a
  GT -> Right $ unsafeCoerce $ if fragRepZ a < fragRepZ b then a else shiftFragRep decr a
  where
  decr i = i - 1

shiftFragRep :: (FragEQ a fr ~ ('Nil :+ '())) => (Int -> Int) -> FragRep fr a -> FragRep fr a
{-# INLINE shiftFragRep #-}
shiftFragRep = \f -> fromOffset . repack . (\(MkHeapKnownFragCardD i) -> MkHeapKnownFragCardD $! f i) . unpack . toOffset

-- | Compare to the @Lacks@ axiom from Gaster and Jones.
narrowFragRep' :: (SetFrag fr ~ '()) => a :/~: b -> FragRep (fr :+ b) a -> FragRep (fr :+ b) b -> FragRep fr a
{-# INLINE narrowFragRep' #-}
narrowFragRep' MkApart a b = case narrowFragRep a b of
  Left _ -> error "narrowFragRep' impossible!"
  Right x -> x

testFragRepNil :: FragRep fr a -> Maybe (FragLT a fr :~: 'Nil)
testFragRepNil frep
  | 0 == fragRepZ frep = Just $ unsafeCoerce Refl
  | otherwise = Nothing

-- | If @b@ is the minimum of @p :+ b@ then either @a@ or @b@ is the minimum of @p :+ b :+ a@.
axiom_minimum :: (
    FragLT b p ~ 'Nil,FragEQ b p ~ 'Nil
  ) =>
    FragRep (p :+ b :+ a) a -> proxy1 p f -> proxy2 b -> SetFrag p :~: '()
  ->
    Either
      ('Nil :~: FragLT a (p :+ b))
      ('Nil :~: FragLT b (p :+ a),FragRep (p :+ a) a,a :/~: b)
{-# INLINE axiom_minimum #-}
axiom_minimum frep _ _ !_pset
  | 0 == fragRepZ frep = Left (unsafeCoerce Refl)
  | otherwise = Right (
      unsafeCoerce Refl
    ,
      case frep of MkFragRep -> unsafeCoerce (shiftFragRep decr frep)
    ,
      unsafeCoerce (MkApart :: 'False :/~: 'True)
    )
  where
  decr i = i - 1

-- | Assuming @b@ is the minimum of @q :+ a@, then @a ~ b@ or @b < a@.
axiom_minimum2 ::
    (
      FragLT b (q :+ a) ~ 'Nil
    ,
      FragEQ b (q :+ a) ~ ('Nil :+ '())
    )
  =>
    proxyq q
  ->
    SetFrag (q :+ a) :~: '()
  ->
    FragRep (q :+ a) a -> proxyb b
  ->
    Either
      (a :~: b)
      (FragRep (q :+ a :- b) a,FragLT b q :~: 'Nil)
axiom_minimum2 _ !_qset frep _
  | 0 == fragRepZ frep = Left (unsafeCoerce Refl)
  | otherwise = Right (
      case frep of MkFragRep -> unsafeCoerce (shiftFragRep decr frep)
    ,
      unsafeCoerce Refl
    )
  where
  decr i = i - 1

-- | Assuming @b@ is the minimum of @q :+ a@, then @a ~ b@ or @b < a@.
axiom_minimum3 ::
    (FragLT a p ~ 'Nil,FragLT b p ~ 'Nil)
  =>
    proxyp p -> proxya a -> proxyb b -> a :~: b
axiom_minimum3 _ _ _ = unsafeCoerce Refl


toOffset :: FragRep fr a -> KnownFragCardD fr a
toOffset MkFragRep = MkKnownFragCardD

fromOffset :: (FragEQ a fr ~ ('Nil :+ '())) => KnownFragCardD fr a -> FragRep fr a
fromOffset MkKnownFragCardD = MkFragRep

unpack :: KnownFragCardD fr a -> HeapKnownFragCardD fr a
unpack = unsafeCoerce

repack :: HeapKnownFragCardD fr a -> KnownFragCardD fr a
repack = unsafeCoerce

data KnownFragCardD :: Frag k -> k -> * where MkKnownFragCardD :: KnownFragCard (FragLT a fr) => KnownFragCardD fr a

-- THIS MUST HAVE THE SAME HEAP REPRESENATION as KnownFragCardD fr
data HeapKnownFragCardD :: Frag k -> k -> * where MkHeapKnownFragCardD :: Int -> HeapKnownFragCardD fr a

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

type (/~) a b = (Apart ('OneApart a b) ~ '())

-----

-- | Ultimately the plugin automate this inference,
-- but it would be costly without knowing which @p@ to use.
--
-- TODO handle apartness at kind @Frag '()@ in plugin,
-- and provide @proxy p -> (FragEQ a p :/~: FragEQ b p) -> a :/~: b@.
apartByFragEQ01 ::
    (FragEQ a p ~ 'Nil,FragEQ b p ~ ('Nil :+ '()))
  =>
    proxyp p -> proxya a -> proxyb b -> a :/~: b
apartByFragEQ01 _ _ _ = unsafeCoerce (MkApart :: 'False :/~: 'True)

-----

-- | INVARIANT: Never reduces to @'JustFragPop' _ _ 'Nil@.
--
-- WARNING: This family chooses which basis element to pop in a non-deterministic way.
type family FragPop_NonDet (fr :: Frag k) :: MaybeFragPop k where
  FragPop_NonDet 'Nil = 'NothingFragPop
type family FragPush (arg :: MaybeFragPop k) :: Frag k where
  FragPush 'NothingFragPop = 'Nil

data MaybeFragPop k =
    JustFragPop (Frag k) k (Frag ())
  |
    NothingFragPop
