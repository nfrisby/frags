% A Path to Row Types in GHC
% Nicolas Frisby
% 2019 May 2
-----

# Introduction

This document summarizes
a GHC typechecker plugin
that would implement an equational theory derived from free abelian groups
as a practical path towards row types.
The plugin is developed up to a particular point on that path,
after which I only have a sketch.
Even just the currently complete part alone seems useful.

I have a proof-of-concept implementation of this plugin
that I am working to release as open source.
I would be very excited to cooperate with anyone hoping to
refine this work into a GHC patch and a formal publication.
I'm proud of this hobby project result,
but I will need cooperation from active GHC developers to integrate it
with the recent and upcoming changes in GHC, especially dependent types.
My email is *`firstname.lastname@gmail.com`*.

## Acknowledgements

The GHC developer community has been very helpful and encouraging over the few years I've iterated on this.
There are too many to list them all, but
Adam Gundry,
Richard Eisenberg,
Simon Peyton Jones,
Iavor Diatchki,
E.Z. Yang,
Jan van Brügge,
and AntC (?)
have given several helpful answers and conversation.

I would like to thank my employer <https://www.navican.com>
for making it easy for me to release this work as open source.

## Bibliography

* <https://en.wikipedia.org/wiki/Free_abelian_group>, <https://en.wikipedia.org/wiki/Free_abelian_group#Integer_functions_and_formal_sums>
* Baaji <http://christiaanb.github.io/posts/type-checker-plugin/>
* Diatchki <http://yav.github.io/publications/improving-smt-types.pdf>
* Gaster and Jones <http://web.cecs.pdx.edu/~mpj/pubs/polyrec.html>
* Gundry *et al* <https://gitlab.haskell.org/trac/ghc/wiki/Plugins/TypeChecker> (original page lost in GitLab transition?)
* Gundry <http://adam.gundry.co.uk/pub/typechecker-plugins/>, <https://github.com/adamgundry/uom-plugin/>
* Kennedy <http://typesatwork.imm.dtu.dk/material/TaW_Paper_TypesAtWork_Kennedy.pdf>
* Leijen <https://www.microsoft.com/en-us/research/publication/extensible-records-with-scoped-labels/>
* Vytiniotis, Peyton Jones, Schrijvers, and Sulzmann <https://www.microsoft.com/en-us/research/publication/outsideinx-modular-type-inference-with-local-assumptions/>
* van Brügge <https://github.com/ghc-proposals/ghc-proposals/pull/180>

## Teaser

The "hard part" of this work has been finding the right primitives,
specifically ones that interact well with GHC's existing constraint solver
(and how exactly to do that via the plugin interface).
The plugin summarized here makes all of these families and classes work like one would hope,
even with type variables.

```{.haskell}
-- Data kind for signed multisets, "frags".
data Frag k = Nil
-- Add an element.
type family (:+) (fr :: Frag k) (e :: k) :: Frag k where {}
-- Subtract an element.
type family (:-) (fr :: Frag k) (e :: k) :: Frag k where {}

-- Total multiplicity of all elements that are < e.
type family Ante (e :: k) (fr :: Frag k) :: Frag () where {}
-- The frag with the multiplicity of e set to 0.
type family Mask (e :: k) (fr :: Frag k) :: Frag k where {}
-- The multiplicity of e.
type family Mult (e :: k) (fr :: Frag k) :: Frag () where {}

-- Each multiplicity is either 0 or 1.
class Set (fr :: Frag k)
-- No substitution makes these types equivalent.
class (/~) (a :: k) (b :: k)

-- Demote an integer.
class KnownFragZ (fr :: Frag ()) where
  fragZVal :: proxy fr -> Integer
```

For example, the plugin considers `('Nil :+ Int :+ Char) ~ ('Nil :+ Char :+ Int)` tautological
and simplifies `(x :+ [Int]) ~ ('Nil :+ Char :+ [a])` to `(x ~ ('Nil :+ Char),a ~ Int)`.

In particular, these families let the user implement
anonymous extensible type-indexed sums and products
including the following signature excerpt.
Think of `Prod` here as the type of records
in which each field's type is also the field's label.

```{.haskell}
data Prod :: Frag k -> (k -> Type) -> Type where
  MkEmp :: Prod 'Nil f
  MkExt ::
    (Ante e fr ~ 'Nil,Mult e fr ~ 'Nil) =>
    Prod fr f -> f e -> Prod (fr :+ e) f

extend ::
  (KnownFragZ (Ante e fr),Mult e fr ~ 'Nil) =>
  Prod fr f -> f e -> Prod (fr :+ e) f

retract ::
  (KnownFragZ (Ante e fr),Mult e fr ~ 'Nil) =>
  Prod (fr :+ e) f -> (Prod fr f,f e)
```

```{.haskell}
data FragRep :: Frag k -> k -> Type where
  MkFragRep :: KnownFragZ (Ante e fr) => FragRep fr e

testFragRep ::
  (Set fr,Mult e1 fr ~ ('Nil :+ '()),Mult e2 fr ~ ('Nil :+ '())) =>
  FragRep fr e1 -> FragRep fr e2 -> Maybe (e1 :~: e2)
```

These frags and the closed type universes and type-indexed sums/products they enable
capture the most interesting parts of row types, row polymorphism, and records/variants.
Moreover, they seem very useful in their own right.

# Core Frag Syntax and Theory

We declare a fresh data kind for a free abelian group.
We refer to a type term that inhabits the kind as a *frag*.

```{.haskell}
data Frag k = Nil
```

We restrict the frag signature for simplicity.
In particular, there is no group operation or inverse function.
Instead, basis elements can be added to or subtracted from a frag one at a time.

```{.haskell}
type family (:+) (fr :: Frag k) (e :: k) :: Frag k where {}
type family (:-) (fr :: Frag k) (e :: k) :: Frag k where {}
```

We refer to a partial application `:+ a` or `:- a` as a *signed tally*.

The syntactic restriction to tallies instead of the usual group operator ensures that
a frag consists of a sequence of tallies terminated by a *root*,
which is either the identity group element `'Nil` or a type variable.
Any type constructor at the root other than `'Nil` will be ill-kinded.
(This variable might be the flattening skolem for a type family application;
we assume throughout this document that all tally applications have been unflattened.)
This linear chain of tallies simplifies the initial development of the plugin
and still admits the core "order-does-not-matter" functionality of row types
(formally: the operator that composes compositions of tallies is commutative).
(It seems feasible but less obvious how to support the frag group operator and inverse function;
compare to <https://github.com/adamgundry/uom-plugin>.)

**Integers**.
Every inhabitant of the kind `Frag ()` with `'Nil` root
is a signed unary representation of an integer.
For example, the frag `'Nil :- '() :- '()` encodes `-2`.
As does the frag `'Nil :- a :- b` for any types `a` and `b`,
by eta-equivalence at kind `()`.
The frag `'Nil` denotes `0`,
as does `'Nil :+ '() :- '()` by frag-equivalence.

**Signed Multisets**.
More generally, every inhabitant of the kind `Frag k` with `'Nil` root
is a `k`-ornamented signed unary representation of a signed multiset.
For example, the frag `'Nil :+ a :+ a :- b` denotes the multiset `{a: 2,b: -1}`.
If the basis elements `a` and `b` are equivalent,
then the frag `'Nil :+ a :+ a :- b` is equivalent to `'Nil :+ a`, and both denote the singleton set `{a}`.

## Notation

The primary formal content of this document consists of rewrite rules,
with prerequisites written in the style of natural deduction.
The conclusion `P   -->   Q` means that `P` rewrites to `Q`.

We use the symbol `±` when writing rules that can be instantiated for both `:+` and `:-`.
In such a rule, every occurence of `±` corresponds to the same tally symbol, either `+` or `-`,
and `∓` corresponds to the other tally symbol.
Morever, we use `:#` to stand for another tally symbol
that is independent of the instantiation of `±` and `∓`.
This means a rule involving `±` and/or `∓` and `:#` can be instantiated in exactly four ways.
For example, `p :# a :± b :± c :∓ d` in such a rule could be any of the following frags.

```{.haskell}
p :+ a :+ b :+ c :- d
p :+ a :- b :- c :+ d
p :- a :+ b :+ c :- d
p :- a :- b :- c :+ d
```

## Equivalence

Two frags `p` and `q` are equivalent if they have the same multiplicity `p(e) == q(e)` for every basis element `e`.
In particular, equivalence does not regard the order of tallies.
The frag solver therefore reorders such applications for canonicity according to an arbitrary total order on types called `ORDER_FRAGILE`.
Once canonicalized, the rest of GHC will also recognize equivalent frags as equivalent types.
The order `ORDER_FRAGILE` need not be preserved by substitution;
*c.f.* [`GHC's nonDetCmpType`](https://github.com/ghc/ghc/blob/ghc-8.6.4-release/compiler/types/Type.hs#L2276).

```{.haskell}
--------------------- [Tally-Inverse]
p :± a :∓ a   -->   p

a < b in ORDER_FRAGILE
------------------------------- [Tally-Sort]
p :# b :± a   -->   p :± a :# b
```

For similar reasons, we partially canonicalize equivalences at kind `Frag`
by collecting all tallies on one side.

```{.haskell}
--------------------------------------------- [Eq-Frag]
(p :± a) ~ (q :# b)   -->   p ~ (q :# b :∓ a)
```

That rule demonstrates collecting tallies (arbitrarily) on the RHS.
Crucially, it only does so if the RHS already has tallies.
If all tallies were already on the LHS,
the frag solver should simply leave them there.
This is because GHC will flatten the side with the tallies to a flattening skolem.
GHC's orientation rules will then determine
if that skolem should be on the left- or right-hand side.
This causes two complications.

  1. If the frag solver prefers one orientation and GHC's equivalence constraint solver prefers the other
     (*c.f.* [`GHC's swapOverTyVars`](https://github.com/ghc/ghc/blob/8d18a873c5d7688c6e7d91efab6bb0d6f99393c6/compiler/typecheck/TcUnify.hs#L1674)),
     then constraint solving will loop.
     The frag solver must therefore avoid unnecessarily reorienting equivalences.
  1. The frag solver and GHC's equivalence constraint solver may interpret
     the same frag equivalence constraint as different substitutions.
     The frag solver must therefore explicitly manage its own substitution
     that correctly interprets equivalences involving tallies.

**Substitution**.
GHC interprets an equivalence in which the LHS is a type variable
that does not also occur in the RHS
as a substitution mapping for that type variable.
(It may first re-orient that equivalence if both sides are type variables.)
The frag solver interprets an equivalence involving tallies
in which at least one of the sides is rooted by type variable
as a mapping from a type variable root to a frag.
If both roots are type variables,
then the frag solver picks the one that GHC would pick if there were no tallies.
The ability to relocate tallies from one side of an equality to the other
is the primary motivation for using signed tallies.

For example, if `α` and `β` are type variables and `(α :+ a) ~ (β :+ b)`,
then the frag solver will interpret that
as either `α ↦ β :+ b :- a` or `β ↦ α :+ a :- b`,
according to GHC's preference between `α` and `β`.
Let's assume `α` without loss of generality.
Ideally, the frag solver could simply emit `α ~ (β :+ b :- a)`
and GHC would handle the corresponding substitutions.
Unfortunately, this does not work because of flattening.
GHC flattens the side with tallies
to a flattening skolem: `α ~ fsk`.
Depending on the flavor of `α`
(skolem variable, meta (unification) variable, flattening skolem variable, flattening meta variable)
and levels of `α` and `fsk` (might be in the flatten cache with for an outer level),
GHC might or might not reorient to `fsk ~ α` --
effecting the exact opposite of the intended substitution!

# Frag Syntax and Theory

We extend the restricted free abelian group signature one step towards row types
with these additional observers and predicates.
Together `Mask` and `Mult` enable a relatively straight-forward decomposition
of an equivalence constraint at kind `Frag`,
and `Set` bounds a frag's denotation from an arbitrary multiset to a typical set.
The rules also rely on `/~`.

```{.haskell}
type family Mask (e :: k) (fr :: Frag k) :: Frag k where {}
type family Mult (e :: k) (fr :: Frag k) :: Frag () where {}

class Set (fr :: Frag k)
class (/~) (a :: k) (b :: k)
```

## Observers

The type `Mask a p` is equivalent to the frag `q`
where the multiplicity `q(e)` is `p(e)` for every basis element `e` apart from `a` and `q(a)` is `0`.

```{.haskell}
----------------------------- [Mask-Z]
Mask (a :: ()) p   -->   'Nil

----------------------- [Mask-Nil]
Mask a 'Nil   -->  'Nil

-------------------------------- [Mask-Eq]
Mask a (p :± a)   -->   Mask a p

a /~ b
------------------------------------- [Mask-Apart]
Mask a (p :± b)   -->   Mask a p :± b

---------------------------------- [Mask-Mask-Eq]
Mask a (Mask a p)   -->   Mask a p

a < b in ORDER_FRAGILE
------------------------------------------- [Mask-Sort]
Mask b (Mask a p)   -->   Mask a (Mask b p)
```

The type `Mult a p` is equivalent to the integer multiplicity `p(a)`.

```{.haskell}
-------------------------- [Mult-Z]
Mult (a :: ()) p   -->   p

----------------------- [Mult-Nil]
Mult a 'Nil   -->  'Nil

--------------------------------------- [Mult-Eq]
Mult a (p :± a)   -->   Mult a p :± '()

a /~ b
-------------------------------- [Mult-Apart]
Mult a (p :± b)   -->   Mult a p

------------------------------ [Mult-Mask-Eq]
Mult a (Mask a p)   -->   'Nil

a /~ b
---------------------------------- [Mult-Mask-Apart]
Mult a (Mask b p)   -->   Mult a p
```

## Predicates

The predicate `Set p` is satisfied if `0 ≤ p(e) ≤ 1` for every basis element `e`.

```{.haskell}
-------- [Set-Nil]
Set 'Nil

--------------- [Set-One]
Set ('Nil :+ a)

k /~ ()   -- to ensure termination
Set (Mask a p)
Set (Mult a p :± '())
--------------------- [Set-Tally]
Set (p :± (a :: k))
```

The predicate `a /~ b` is satisfied if `a` and `b` are *apart*:
informally, no substitution could map them to equivalent types.

```{.haskell}
---------- [Apart-Head]
TC1 /~ TC2

n > 0
(l_1 /~ r_1) OR (l_2 /~ r_2) OR ... OR (l_n /~ r_n)
tc is an injective type constructor
--------------------------------------------------- [Apart-Inj]
tc l_1 l_2 ... l_n /~ tc r_1 r_2 ... r_n
```

## Derived Basis Element Equivalence and Apartness

The frag signature is rich enough to phrase constraints
that imply/require the equivalence and apartness of involved basis elements.

I don't have a principled way of choosing these rules;
I'm still at the stage of discovering them by pushing the plugin's envelope.
My lack of clarity here drives most of my hesitancy to add support for the group operator.

Some examples include:

  * `Set (Mult a ('Nil :+ b) :- '())` requires `a ~ b`.
  * `Mult a ('Nil :+ b) ~ 'Nil` requires `a /~ b`.
  * `Mask a ('Nil :+ b) ~ 'Nil` requires `a ~ b`.
  * `(Mult a p ~ 'Nil,Mult b p ~ ('Nil :+ '()))` requires `a /~ b`.

**Floating Equalities**.
For soundness,
GHC will not discharge a Wanted equivalence constraint
by unifying a meta variable under "local" equivalence constraints:
equivalence constraints that are brought into scope under the scope of the meta variable.
This is implemented coarsely by tracking the *level* of each type variable,
which is the depth of its `forall` binder.
Thus, GHC floats equivalences out from under `forall` binders when possible,
hoping a floated equivalence will reach a level where GHC is allowed to unify the meta variable.
The basic idea is that GHC doesn't float equivalences out from under equivalences,
because those outer equivalencies may evolve
such that GHC can discharge the inner equivalence without unifying.
This is how a type variable can be equivalent to different types
in different alternatives of a `case` expression with `-XGADTs`.

Because a `Set` class might simplify to an equivalence constraint,
we similarly must prevent equivalence constraints from floating out from under `Set` constraints
-- else GADT patterns that introduce `Set` constraints might malfunction
and cause premature/overly aggressive unification.
We do this in the implementation by making `Set` a type family instead of a class,
and writing `'() ~ Set a` instead of `Set a`.

```{.haskell}
type family Set (fr :: Frag k) :: () where {}
```

It's kind of awkward but pretty simple and works.
I've done the same for `/~` because I'm not sure if it should stop floating.
I suspect it should, since a `/~` constraint can allow a `Set` constraint to simplify to an equivalence.
I'll continue to use the `class` syntax in this document for legibility.

**Typecheck Plugins Feature Idea**.
This workaround would be unnecessary if GHC supported an annotation on a class
that prevented equalities from floating past it.
It seems like this would only be useful in the context of typecheck plugins.

# Frags for Closed Type Universes

We add an observer and an evidenced constraint as another step towards row types;
compare to the conventional `Lacks` constraint of row types
and to the `TypeRep` from `Data.Typeable`.

```{.haskell}
type family Ante (e :: k) (fr :: Frag k) :: Frag () where {}

class KnownFragZ (fr :: Frag ()) where
  fragZVal :: proxy fr -> Integer
```

The type `Ante a p` is the total multiplicity in `p` of all basis elements `e` that are less than `a` in an arbitrary partial order on types called `ORDER_STABLE`.
Unlike `ORDER_FRAGILE`, the order `ORDER_STABLE` is deterministic:
the order relates `a` and `b` only if it relates all substitution instances of them in the same way.
`ORDER_STABLE` is partial because of this requirement,
since it cannot relate some types involving free variables (including flattening skolems) (*e.g.* `[a] ? [b]`).
On the other hand, two types with no free variables are necessarily comparable (*e.g.* `"bar" < "foo"`).
And some types are ordered even with free variables (*e.g.* `[a] < Maybe b`).

```{.haskell}
----------------------------- [Ante-Z]
Ante (a :: ()) p   -->   'Nil

----------------------- [Ante-Nil]
Ante a 'Nil   -->  'Nil

b < a in ORDER_STABLE
--------------------------------------- [Ante-Eq]
Ante a (p :± b)   -->   Ante a p :± '()

b ≥ a in ORDER_STABLE
-------------------------------- [Ante-Apart]
Ante a (p :± b)   -->   Ante a p
```

The value `fragZVal (Proxy :: Proxy p)` is the value-level demotion of the type-level integer `p`.

```{.haskell}
--------------------------------------- [Z-Nil]
fragZVal (Proxy :: Proxy 'Nil)   ==   0

-------------------------------------------------------------------------- [Z-Tally]
fragZVal (Proxy :: Proxy (p :± a))   ==   fragZVal (Proxy :: Proxy p) :± 1
```

Note that those two rules are inveritble; in particular,
the plugin applies `[Z-Tally]` to Givens in one direction and to Wanteds in the opposite direction.

**Minima**.
The constraints `(Set p,Ante a p ~ 'Nil,Mult a p ~ ('Nil :+ '())` imply that `a` is the minimum element in `p`.
It is important that `ORDER_STABLE` implies any two minima of the same set are necessarily equivalent.
(`Set` could be relaxed to "all multiplicities are non-negative" without spoiling the uniqueness of minima.
This seems somewhat related to Leijen's "scoped labels".)

# Use Case: Set Types

Because `ORDER_STABLE` minima are unique,
the frag solver enables users to safely apply this `testFragRep` function,
part of the Trusted Code Base.

```{.haskell}
data FragRep :: Frag k -> k -> Type where
  MkFragRep :: KnownFragZ (Ante e fr) => FragRep fr e

mkFragRep ::
  KnownFragZ (Ante e fr) =>
  proxy1 fr -> proxy2 e -> FragRep fr e
mkFragRep _ _ = MkFragRep

fragRepOffset ::
  forall e fr.
  (Set fr,Mult e fr ~ ('Nil :+ '()))
  FragRep fr e -> Int
fragRepOffset MkFragRep = fragZVal (Proxy :: Proxy (Ante e fr))

testFragRep ::
  (Set fr,Mult e1 fr ~ ('Nil :+ '()),Mult e2 fr ~ ('Nil :+ '())) =>
  FragRep fr e1 -> FragRep fr e2 -> Maybe (e1 :~: e2)
testFragRep rep1 rep2
  | fragRepOffset rep1 == fragRepOffset rep2 =
    Just (unsafeCoerce Refl)
  | otherwise = Nothing
```

Such closed type universes with testable type equivalence
enable the definition of set-indexed sums and products.
These are likely more familiar if viewed as simplifications
of row-indexed polymorphic variant and record types
where each column's image is also the column's label.
Hence the indicative name *set types* for constrained frags,
compared to row types.

The implementation of the following signatures
requires some additional Trusted Code Base functions
that I'm still working out,
so I'm eliding the implementation in this write-up.
They primarily generalize `testFragRep` to also strengthen/weaken `FragRep` offsets;
returning `Left (rep' :: FragRep (fr :- e2) e1)` instead of `Nothing`.

## Extensible Anonymous Sums

```{.haskell}
data Sum :: Frag k -> (k -> Type) -> Type where
  MkSum ::
    (KnownFragZ (Ante e fr),Mult e fr ~ ('Nil :+ '())) =>
    f e -> Sum fr f

sum_proof :: Sum 'Nil f -> a
sum_proof x = case x of {}

box :: f e -> Sum ('Nil :+ e) f
box = inject

inject ::
  (Set fr,KnownFragZ (Ante e fr),Mult e fr ~ 'Nil) =>
  f e -> Sum (fr :+ e) f
inject = MkSum

narrow ::
  (Set fr,KnownFragZ (Ante e fr),Mult e fr ~ 'Nil) =>
  Sum fr f -> Either (Sum (fr :- e) f) (f e)

widen ::
  (Set fr,KnownFragZ (Ante e fr),Mult e fr ~ 'Nil) =>
  proxy e -> Sum fr f -> Sum (fr :+ e) f
```

## Extensible Anonymous Products

Variations of this data structure can be implemented with more compact memory layouts
by relying on `fragRepOffset` and `unsafeCoerce`.

```{.haskell}
data Prod :: Frag k -> (k -> Type) -> Type where
  MkEmp :: Prod 'Nil f
  MkExt ::
    (Ante e fr ~ 'Nil,Mult e fr ~ 'Nil) =>
    !(Prod fr f) -> f e -> Prod (fr :+ e) f

prod_proof :: Prod fr f -> (Set fr => r) -> r

unbox :: Prod ('Nil :+ e) -> f e
unbox = snd . retract

extend ::
  (KnownFragZ (Ante e fr),Mult e fr ~ 'Nil) =>
  Prod fr f -> f e -> Prod (fr :+ e) f

retract ::
  (KnownFragZ (Ante e fr),Mult e fr ~ 'Nil) =>
  Prod (fr :+ e) f -> (Prod fr f,f e)

prod_map ::
  (forall a. f a -> g a) -> Prod fr f -> Prod fr g
prod_foldMap ::
  Monoid m => (forall a. f a -> m) -> Prod fr f -> m

-- | Traversed in ORDER_STABLE order.
prod_traverse ::
  Applicative i =>
  (forall a. f a -> i (g a)) -> Prod fr f -> i (Prod fr g)

prod_zip ::
    (forall a. f a -> g a -> h a)
  -> Prod fr f -> Prod fr g -> Prod fr h
```

# Sketch: Naturals

(My prototype currently implements everything prior to this section.)

The plugin should also implement the following families.

```{.haskell}
-- Total multiplicity of all elements.
type family FragCard (fr :: Frag k) :: Frag () where {}
-- Only reduces for non-negative integers.
type family FragNat (fr :: Frag ()) :: Nat where {}
```

# Sketch: Constraining Frags

The use of type families to realize the "syntax" of tallies
prevents frags from indexing type class instances.
This seems appropriate since frags are purely structural types.
However, it does seem natural to individually constrain each basis element *within* a frag.

The `Pop` and `Push` observers and the `AllFrag` predicate transformer
let us constrain each basis element that has a non-zero multiplicity.
A more general constraint might also constrain the multiplicities,
but that seems beyond our initial scope of interest.

```{.haskell}
type family Pop (fr :: Frag k) :: MaybePop k where {}
type family Push (arg :: MaybePop k) :: Frag k where {}
class AllFrag (pred :: k -> Constraint) (fr :: Frag k)
class AllMaybePop (pred :: k -> Constraint) (fr :: MaybePop k)

data MaybePop k =
    JustPop (Frag k) k (Frag ())
  |
    NothingPop
```

The `Pop` type family splits off an **arbitrary** basis element with non-zero multiplicity.
A related type family that pops off the `ORDER_STABLE`-minimum basis element is likely important to also have.

```{.haskell}
---------------------------- [Pop-Nil]
Pop 'Nil   -->   'NothingPop

'Nil :∓ '() ~ Mult e fr
---------------------------- [Pop-Zero]
Pop (fr :± e)   -->   Pop fr

'Nil :∓ '() /~ Mult e fr
--------------------------------------------------------------- [Pop-NonZero]
Pop (fr :± e)   -->   'JustPop (Mask e fr) e (Mult e fr :± '())

------------------------- [Pop-Push]
Pop (Push arg)   ->   arg
```

The `Push` type family is creating frags, not observing them,
and so only requires plugin support for the `[Push-Pop]` rule.

```{.haskell}
----------------------------- [Push-Nil]
Push 'NothingPop   -->   'Nil

------------------------------------ [Push-Zero]
Push ('JustPop fr e 'Nil)   -->   fr

------------------------------------------------------------------- [Push-NonZero]
Push ('JustPop fr e (z :± a))   -->   Push ('JustPop (fr :± e) e z)

----------------------- [Push-Pop]
Push (Pop fr)   ->   fr
```

The `AllFrag` and `AllMaybePop` classes do not need plugin support;
simple `instance`s suffice, since `Pop` is doing the heavylifting.

```{.haskell}
AllMaybePop pred (Pop fr)
--------------------------
AllFrag pred fr

-----------------------------
AllMaybePop pred 'NothingPop

pred e
AllFrag pred fr
-----------------------------------------------
AllMaybePop pred ('JustPop fr e nonzero_count)
```

## Evidence

Any satisfied `(Set fr,AllFrag pred fr)` constraint should also be evidenced by a `Prod fr (Dict1 pred)`,
but I haven't worked through these details yet.

```{.haskell}
data Dict1 :: (k -> Constraint) -> k -> Type where
  MkDict1 :: pred a => Dict1 pred a
```

```{.haskell}
class Set fr => DictProd (pred :: k -> Type) (fr :: Frag k)
  dictProd :: Prod fr (Dict1 pred)
```

(Note: The implementation of `DictProd` will involve an auxiliary class
with a method with a type involving `Push`.)

Together, `prod_zip` and `prod_pure` provide an `Applicative`-like interface to `Prod`.

```{.haskell}
prod_dict :: DictProd pred fr => proxy pred -> (forall a. pred a => f a) -> Prod fr f

prod_pure :: (DictProd None fr) => (forall a. f a) -> Prod fr f
prod_pure = prod_dict (Proxy :: Proxy None)

class    None (a :: k)
instance None (a :: k)
```

**Alternative**.
Perhaps `Set` should ultimately be defined in terms of `DictProd`.
Though that would seem to require that plugin be aware of the `Prod` signature,
which is currently defined in user space.
Moreover, `Prod` ultimately admits implementations with different heap layouts,
and I hesitate to commit to one for `dictProd`.

# Sketch: Use Case: Row Types

We sketch the following interface to rows for the purpose of reusing the frag solver,
but a separate row solver that does not directly reuse the frag signature
is likely to provide a better user experience.

The basic idea is to use frags to synchronize two row's labels,
and then use a simple "lookup" type family to unify the image of each label in both rows.
This two-stage approach can use signed tallies
for substition/unification in the constraint solver
without needing to consider "signed row extension",
whatever that might mean.

(It seems interesting to index the row kind by the frag of its labels,
but without being able to promote the constraints limiting that frag to a set,
I'm not seeing the benefit.)

```{.haskell}
data Row (k :: Type) (v :: Type) = Emp
type family Ext (rho :: Row k v) (lbl :: k) (img :: v) :: Row k v where {}

type family Dom (rho :: Row k v) :: Frag k where {}
type family Get (lbl :: k) (rho :: Row k v) :: v where {}
```

```{.haskell}
Dom l ~ Dom r   -- N.B. at kind Frag k
AllFrag (UnifyAt l r) (Dom l)
----------------------------- [Eq-Row]
l ~ r

class    (Get lbl l ~ Get lbl r) => UnifyAt (l :: Row k v) (r :: Row k v) (lbl :: k)
instance (Get lbl l ~ Get lbl r) => UnifyAt (l :: Row k v) (r :: Row k v) (lbl :: k)
```

## Observers

```{.haskell}
-------------------- [Dom-Nil]
Dom 'Emp   ->   'Nil

------------------------------------------- [Dom-Ext]
Dom (Ext rho lbl img)   ->   Dom rho :+ lbl
```

```{.haskell}
------------------------------------ [Get-Eq]
Get lbl (Ext rho lbl img)   ->   img

lbl1 /~ lbl2
----------------------------------------------- [Get-Apart]
Get lbl1 (Ext rho lbl2 img)   ->   Get lbl1 rho
```

# Caveat

Many of the rules are simpler than they ultimately must be.
For example, `Ante a (Mask b ('Nil :+ a))`
should reduce to `'Nil` regardless of how `a` and `b` relate.
And `Mult a (p :+ b)` should simplify to `Mult a ('Nil :+ b) :- '()`
if we also have `Mult a p ~ ('Nil :- '())`.

I left out these details and similar because
the current rules are much lighter this way
and still convey the principal ideas.
