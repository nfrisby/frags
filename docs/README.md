# Documentation for `frag` and `motley`

This file always contains the latest official documentation
for the `frag` and `motley` libraries.

# Table of Contents

  * [Meta][sec:meta]
  * [`frag` API][sec:frag-api]
      * [Introduction forms and equivalence][sec:frag-intro-and-eq]
      * [Integers][sec:frag-integers]
      * [Sets][sec:frag-sets]
      * [Frag polymorphism][sec:frag-polymorphism]
      * [Universes][sec:frag-universes]
      * [Nominal view][sec:frag-nominal-view]
      * [Auxiliaries][sec:frag-auxiliaries]
  * [`motley` API][sec:motley-api]
      * [Sums][sec:motley-sums]
      * [Products][sec:motley-products]
      * [Combinators][sec:motley-combinators]
  * [Internals][sec:internals]
    * [Frag semantics][sec:internals-semantics]
    * [Rules][sec:internals-rules]
    * [Normalization][sec:internals-normalization]
    * [Floating equivalences][sec:internals-floating-eqs]
    * [Flattening][sec:internals-flattening]

# Meta
[sec:meta]: #meta

## Context for this work

I've developed this typechecker plugin as a hobby passion project over the last few years.
The aim has always been twofold:
to learn about GHC's type checker
and to make a proof-of-concept compelling enough that
an active GHC developer/researcher could not resist the urge
to distill a proper GHC patch out of it for *row polymorphism*.
I've learned a lot, and there's thankfully no end in sight on that front.
And of the several from-scratch iterations I've done in private,
I'm delighted to finally share one that feels promising!

This repository was, is, and will remain a hobby project.
My work on it will continue to be bursty.
I'm excited to cooperate with you!
But my bandwidth is limited :(

## About this documentation

We must maximize how accurate, available, and approachable the docs feel
to readers and authors alike.

  * I'm tracking docs alongside the source in a single repository,
    prioritizing accuracy over Git precision.

  * I'm using a single monolithic file
    instead of adding dependencies on frameworks like Sphinx or MkDocs,
    prioritizing availablility over aesthetics and Git precision.
    (TODO Can I get some kind of linting for intra-document refs? Otherwise separate files docs might be better.)

  * I'm using <https://github.github.com/gfm/> because of its general prevalence,
    prioritizing approachability over other formats' technical advantages.

## Contributing to this project

Please find or create a GitHub Issue on which to discuss your idea;
I'd like to keep the higher-level discussions there
and dig into the details on the PRs.

## Acknowledgements

The GHC developer community has been very helpful and encouraging
over the few years I've iterated on this.
There are too many to list them all, but
Simon Peyton Jones,
Adam Gundry,
Richard Eisenberg,
Iavor Diatchki,
E.Z. Yang,
Jan van Brügge,
and AntC (?)
have given several answers, conversation, and encouragement that helped a lot.

I deeply appreciate that my employer <https://www.navican.com>
made it easy for me to release this work as open source.

## Bibliography

* <https://en.wikipedia.org/wiki/Free_abelian_group>,
  <https://en.wikipedia.org/wiki/Free_abelian_group#Integer_functions_and_formal_sums>
* Baaji <http://christiaanb.github.io/posts/type-checker-plugin/>
* Diatchki <http://yav.github.io/publications/improving-smt-types.pdf>
* Gaster and Jones <http://web.cecs.pdx.edu/~mpj/pubs/polyrec.html>
* Gundry *et al* <https://gitlab.haskell.org/trac/ghc/wiki/Plugins/TypeChecker> (original page lost in GitLab transition?)
* Gundry <http://adam.gundry.co.uk/pub/typechecker-plugins/>, <https://github.com/adamgundry/uom-plugin/>
* Kennedy <http://typesatwork.imm.dtu.dk/material/TaW_Paper_TypesAtWork_Kennedy.pdf>
* Leijen <https://www.microsoft.com/en-us/research/publication/extensible-records-with-scoped-labels/>
* Vytiniotis, Peyton Jones, Schrijvers, and Sulzmann <https://www.microsoft.com/en-us/research/publication/outsideinx-modular-type-inference-with-local-assumptions/>
* van Brügge <https://github.com/ghc-proposals/ghc-proposals/pull/180>

# `frag` API
[sec:frag-api]: #frag-API

The `frag` library declares the `Frag b` data kind,
its interface,
and a typechecker plugin that implements its equational theory.

## Frags and their equivalence
[sec:frag-intro-and-eq]: #frags-and-their-equivalence

The library declares the following introduction forms.
Because of the plugin, the type families are not as much of a hindrance as one usually expects --
they behave like something in between type constructors and type families
similar to *injective type families* (<https://gitlab.haskell.org/ghc/ghc/issues/6018>).
(See the [Frag polymorphism][sec:frag-polymorphism] section below for more information.)

```haskell
data Frag (b :: k) = 'Nil
infixl 6 :+,:-
type family (fr :: Frag b) :+ (e :: b) :: Frag b where {}
type family (fr :: Frag b) :- (e :: b) :: Frag b where {}
```

The kind `Frag b` denotes all finite signed multisets of `b`s.
The element multiplicities in a *signed* multiset can be negative.
There are only finitely many non-zero multiplicities in a *finite* multiset.
Example frags:

```haskell
'Nil :+ Int :+ Int :- Char :: Frag Type   -- {Int: 2,Char: -1}

'Nil :+ 1 :+ 2 :- 13 :: Frag Nat   -- {1: 1,2: 1,13: -1}

'Nil :+ "docker" :+ "sudo" :: Frag Symbol   -- {"docker": 1,"sudo": 1}
```

(Until <https://gitlab.haskell.org/ghc/ghc/issues/13637> is resolved,
GHC messages will unfortunately use unnecessary parens as in `(('Nil :+ 1) :+ 2) :- 13`.)

Although a frag denotes a multiset,
the current frag interface currently omits union, intersection, and all other binary operators.
Multisets can only be built by incrementing or decrementing multiplicities one at a time.
(See <https://github.com/nfrisby/frags/issues/25>.)
We call a right partial application `:+ e` or `:- e` a *signed tally*.

The typechecker plugin lets GHC simplify equivalences at kind `Frag b`.
In particular, it ensures that the order of tallies does not matter.
Example frag equivalences that the plugin can simplify:

```haskell
(('Nil :+ Int :- Int)   ~   'Nil)

(('Nil :+ Int :+ Char)   ~   ('Nil :+ Char :+ Int))

(('Nil :+ x :+ y :- x)   ~   ('Nil :+ y))

(('Nil :+ x :+ Int)   ~   ('Nil :+ Int :+ y))   -- simplified to (x ~ y)
```

(I think we'll need those inner parentheses until <https://gitlab.haskell.org/ghc/ghc/issues/10056> is resolved.)

Those last examples involve type variables,
foreshadowing [*frag polymorphism*][sec:frag-polymorphism].

## Frag integers
[sec:frag-integers]: #frag-integers

The kind `Frag ()` denotes the integers, **Z**.
Example integer frags:

```haskell
'Nil   -- 0

'Nil :+ '()   -- 1

'Nil :+ '() :+ '()  -- 2

'Nil :- '() :- '()  -- negative 2
```

This approach lets the library conveniently declare the `FragEQ` elimination form,
which reduces a frag to the (integer) multiplicity of the specific element.

```haskell
type family FragEQ (e :: b) (fr :: Frag b) :: Frag () where {}
```

Example multiplicity constraints that the plugin can simplify:

```haskell
FragEQ e 'Nil ~ 'Nil

FragEQ Int (fr :+ Char) ~ FragEQ Int fr

FragEQ e (fr :- e) ~ FragEQ e fr :- '()

FragEQ Int ('Nil :+ x) ~ ('Nil :+ '())   -- simplified to (x ~ Int)
```

## Sets
[sec:frag-sets]: #sets

Sets are multisets with binary multiplicities, `0` or `1`.
We introduce a methodless type class for that predicate.

```haskell
class SetFrag (fr :: Frag b) where {}
```

Example set constraints that the plugin can simplify:

```haskell
SetFrag ('Nil :+ Int :+ Char)

SetFrag ('Nil :+ x :- y)   -- simplified to (x ~ y)
```

### Workaround

For technical reasons, we currently need set constraints to be `~` constraints.
We therefore write `SetFrag fr ~ '()` instead of `SetFrag fr`.
The essential semantics are the same,
but GHC now handles unification in the scope of *local* set constraints
arising from GADT pattern matches.
(FYI, understanding <https://gitlab.haskell.org/ghc/ghc/issues/15009> really claried this aspect of *OutsideIn(X)* for me.)

```haskell
type family SetFrag (fr :: Frag b) :: () where {}
```

## Frag polymorphism
[sec:frag-polymorphism]: #frag-polymorphism

The plugin interprets and simplifies non-trivial relationships
between type variables at kind `Frag b`,
thereby implementing *frag polymorphism*.

Frag polymorphism allows the user to write signatures
that GHC without the plugin would report as ambiguous.

```haskell
frpo_fun :: Proxy (fr :+ x) -> Proxy fr
```

In that signature, the type variable `x` only occurs
as an argument to a type family application.
And that family was not declared injective in that argument,
so GHC without the plugin would not be able to infer `x` at occurrences of `frpo_fun`.
Hence it rightly rejects the signature (without `-XAllowAmbiguousTypes`).
However, with the plugin, GHC can infer `x` (at well-typed use sites).
Examples:

```haskell
frpo_fun (Proxy :: Proxy ('Nil :+ Int))
  -- infers (fr ~ 'Nil,x ~ Int)

frpo_fun (Proxy :: Proxy 'Nil) :: Proxy ('Nil :- Int)
  -- infers (x ~ Int,fr ~ ('Nil :- Int))
```

The above is not very transparent, with all the proxies.
The section below on [`motley` products][sec:motley-products] will be more recognizable as comparable to row polymorphism.
However, that does ultimately arise from the above behavior.
The next sections introduces a another stepping stone towards the more familiar data structures.

## Universes
[sec:frag-universes]: #universes

Informally, *universe* is type theory terminology for "set of types".
Following the [Sets as frags][sec:frag-sets] section,
we can use a frag as a universe.
Universes tend to support an additional interface,
specifically a "code" data type that is one-to-one with types in the universe.
(Find more details in any resource discussing *universes a la Tarski*.)

The GHC ecosystem already includes support for universes.

  * The kind `Type` is a "set of types", but it doesn't have codes.
    The `Typeable` class does and thereby determines a universe (subuniverse of `Type`).
    In particular, it is an *open* universe:
    any `data` declaration adds correspoding codes and types to it.
    (See the [GHC User's Guide](https://downloads.haskell.org/~ghc/8.6.5/docs/html/users_guide/glasgow_exts.html#deriving-typeable-instances) for details.)

  * This `ExampleU` GADT defines codes for the (sub)universe containing `Char` and `Int`.

    ```haskell
    data ExampleU :: Type -> Type where
      ExampleU_Char :: ExampleU Char
      ExampleU_Int :: ExampleU Int
    ```

    Unlike the `Typeable` universe, this universe is *closed*:
    no declaration can create more codes.

  * Universe are a core concept in the `singletons` package's encoding of dependent types.

The `frag` library and plugin introduce novel universes
that are more precise than any in the GHC ecosystem.
It relies on two additional elimination forms.

```haskell
type family FragLT (e :: b) (fr :: Frag b) :: Frag () where {}
class KnownFragCard (fr :: Frag ()) where
  fragCard :: proxy fr -> Int   -- NB plugin grinds to halt well before this overflows
```

The `FragLT e fr` application denotes the total multiplicity
of all elements `x` in `fr` such that `x < e`.
That `<` sign refers to a strict partial order on types that we call `ORDER_STABLE`.
How exactly it relates types is an implementation detail of GHC and the plugin.
It has a few key properties that make it safe for our use here too.

  * It relates `a` and `b` only if it relates all substitution instances of them in the same way.
    This is why it is a partial order.

  * On the other hand, two types with no free variables are necessarily comparable (maybe `"bar" < "foo"`).
    It even orders some types with free variables (maybe `[a] < Maybe b`).

  * I have not thought about how it would handle impredicative types;
    I suggest not trying that out :).

  * Any non-empty set of pairwise-related types has a unique minimum according to `ORDER_STABLE`.

The `fragCard` method demotes the type-level integer to the value-level.

With `SetFrag`, `FragLT`, and `KnownFragCard`,
we can declare a data type for a frag universe's codes
and functions on them.

```haskell
data Place :: Frag b -> b -> * where
  MkPlace ::
      (FragEQ e fr ~ ('Nil :+ '()),KnownFragCard (FragLT e fr))
    =>
      Place fr e

testEquality_Place ::
  SetFrag fr ~ '() => Place fr x -> Place fr y -> Maybe (x :~: y)
```

Note the set constraint in the type of `testEquality_Place`:
this coercion is only safe if all of the multiplicities in `fr` are non-negative.
`SetFrag` is all we have at hand,
but positive multiplicities greater than `1` would be fine here.

There are several additional useful functions over `Place`.
For example, if `y` is the minimum of `fr :+ y`,
then we can embed `Place fr x` into `Place (fr :+ y) x`.
(Operationally, this increments the integer in the `KnownFragCard` dictionary.)

```haskell
widenPlaceByMin :: (FragLT y fr ~ 'Nil) => proxyy y -> Place fr x -> Place (fr :+ y) x
```

I've included these axia in `Data.Frag` as I discover I need them --
see the Haddock in that module regarding the `:<:` evidence.
Their variety seems somewhat sundry at the moment.
Eventually it may be appropriate for the the plugin to automate such reasoning
instead of forcing the user to manually prove relations.
Right now, the axia seem to be necessary mostly to only very generic frag-based code,
such as the `motley` package implementation,
so I'm favoring keeping the plugin simpler.

## Nominal view
[sec:frag-nominal-view]: #nominal-view

TODO elaborate

For the sake of constraining elements of frag,
the plugin is able to decompose a frag by its support.
As soon as the plugin determines the exact multiplicity of a basis element in the support of `fr`,
it can reduce `FragPop_NonDet fr` to `'JustFragPop (FragPop_NonDet (FragNE e fr)) e m`,
in which `m` is the multiplicity of `e` in `fr`.
(The plugin implementation does not yet reduce this as soon as possible;
for simplificy, it currently defers until the whole support is known --
see <https://github.com/nfrisby/frags/issues/11>.)

```haskell
type family FragPop_NonDet (fr :: Frag k) :: MaybeFragPop k where {}

type family FragPush (mpop :: MaybeFragPop k) :: Frag k where {}

data MaybeFragPop k =
    JustFragPop (Frag k) k (Frag ())
  |
    NothingFragPop
```

Importantly, the plugin also reduces `FragPush (FragPop_NonDet fr)` to `fr`.

## Auxiliaries
[sec:frag-auxiliaries]: #auxiliaries

If only because of implementation details,
the following types are relevant to the user.

### Frag masking

The library provides the following elimination form.

```haskell
type family FragNE (e :: b) (fr :: Frag b) :: Frag b where {}
```

The multiplicities of `FragNE e fr` agree with those of `fr` except on `e`,
which has a multiplicity of `0`.
Thus, `FragNE e` removes `e` from `fr`'s *support*,
the *set* of elements with non-zero multiplicities.

(Observation: A set frag is equivalent to its own support.
This could be an interesting way to re-consider `SetFrag p`: `p ~ Support p`.)

### Apartness constraints

For `'Nil :+ x :+ y` to be a set, `x` and `y` must not be the same type.
In jargon, `x` and `y` must be *apart*.
Unfortunately, the GHC constraint solver does not treat apartness constraints,
and neither do any other plugins.
They are crucial to the frag theory,
and so the frag plugin handles them.

```haskell
class Apart (pairs :: ApartPairs)   -- Satisfied if any pair is apart

data ApartPairs =
    forall k.
    ConsApart k k ApartPairs
  |
    forall k.
    OneApart k k

type (/~) a b = Apart ('OneApart a b)
data (:/~:) a b = (a /~ b) => MkApart
```

Example apartness constraints that the plugin can simplify:

```haskell
Apart ('OneApart Int Char)

Apart ('OneApart [x] [y])   -- simplified to Apart ('OneApart x ~ y)

Apart ('ConsApart Int Char ('OneApart Bool Bool))

Apart ('ConsApart Bool Bool ('OneApart Int Char))   -- order is irrelevant
```

# `motley` API
[sec:motley-api]: #motley-api

The `motley` library uses the frag polymorphism and frag universes of the `frag` library
to define n-ary type-indexed sums and products.
I'm continually amazed that the relatively simple frag interface suffices for defining the following data types.

I chose the name "motley" because the data types are *structural*, *extensible*, *anonymous*, etc --
they are *patchwork* compositions of basis elements, reminiscent of a quilt.

## Sums
[sec:motley-sums]: #sums

Sums are just a tag and a payload.
Recognize these as a less general form of row-indexed polymorphic variants.

```haskell
data Sum :: Frag b -> (b -> *) -> * where
  MkSum :: Place fr e -> f e -> Sum fr f
```

The tag is the place of the basis element `e` in the frag `fr`.
Recall that this place is most useful when `fr` is has no negative multiplicities.
Therefore, most of the interface to `Sum`s will require `SetFrag fr`.

We construct sums trivially via injection,
simply tagging a summand value with its place in the frag.

```haskell
inj :: (FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p)) => f a -> Sum (p :+ a) f
inj = MkSum MkPlace
```

And we deconstruct them by discriminating on their tag.
Note the `SetFrag p` constraint on `alt`
and that the plugin (if correct) will ensure each occurrence of `absurd` is unreachable.

```haskell
absurd :: String -> Sum 'Nil f -> a
absurd = \s _ -> error $ "absurd Sum: " ++ s

alt ::
    (SetFrag p ~ '(),FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p))
  =>
    (Sum p f -> ans) -> (f a -> ans) -> Sum (p :+ a) f -> ans
```

Note in particular that `alt Left Right` maps `Sum (p :+ a) f` to `Either (Sum p f) (f a)`.

## Products
[sec:motley-products]: #products

Products are dual to sums.
Recognize these as a less general form of row-indexed records.

```haskell
data Prod :: Frag b -> (b -> *) -> * where
  MkCons ::
      (FragLT e fr ~ 'Nil,FragEQ e fr ~ 'Nil)
    =>
      Prod fr f -> f e -> Prod (fr :+ e) f
  MkNil :: Prod 'Nil f
```

By a simple induction, a product proves that its index is a set:
the inductive step follows from `FragEQ e fr ~ 'Nil`.

```haskell
proofProd :: Prod fr f -> SetFrag fr :~: '()
```

We construct products by extending one with a new *factor* (a.k.a. field).

```haskell
nil :: Prod 'Nil f
nil = MkNil

ext ::
    (FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p))
  =>
    Prod p f -> f a -> Prod (p :+ a) f
```

And we deconstruct them by retracting one factor at a time.

```haskell
ret ::
    (FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p))
  =>
    Prod (p :+ a) f -> (Prod p f,f a)

prj ::
    (FragEQ a p ~ 'Nil,KnownFragCard (FragLT a p))
  =>
    Prod (p :+ a) f -> f a
prj = snd . ret
```

The `FragLT e fr ~ 'Nil` constraint on `MkCons` ensures
that the order of the factor in the linked list is canonical.

This implementation as a linked list is inefficient,
but demonstrates the expressivity of the simple frag interface.
Other data structures for products can have usefully different layouts in memory.
For example, <https://github.com/nfrisby/frags/issues/9> will investigate "flat" memory representations,
such as the "short vector" used in one of my deprecated earlier iterations, <https://github.com/coxswain>.

## Combinators
[sec:motley-combinators]: #combinators 

Sums and products admit many useful combinators,
both separately and together.
For example:

```haskell
newtype (f ~> g) a = MkFun{appFun :: f a -> g a}

updateSum :: Prod fr (f ~> g) -> Sum fr f -> Sum fr g
updateProd :: Sum fr (Compose Endo f) -> Prod fr f -> Prod fr f
```

They both provide optics à la `lens`.

```haskell
opticSum ::
    (
	  SetFrag fr ~ '()
    ,
	  FragEQ x fr ~ 'Nil,KnownFragCard (FragLT x fr)
    ,
	  FragEQ y fr ~ 'Nil,KnownFragCard (FragLT y fr)
    )
  =>
    Prism.Prism (Sum (fr :+ x) f) (Sum (fr :+ y) f) (f x) (f y)

opticProd ::
    (
      FragEQ x fr ~ 'Nil,KnownFragCard (FragLT x fr)
    ,
      FragEQ y fr ~ 'Nil,KnownFragCard (FragLT y fr)
    )
  =>
    Lens.Lens (Prod (fr :+ x) f) (Prod (fr :+ y) f) (f x) (f y)
```

Products have an `Applicative` like interface,
using the obvious generalizations from `* -> *` to `(* -> *) -> *`.

```haskell
zipWithProd ::   -- <*>
  (forall a. f a -> g a -> h a) -> Prod fr f -> Prod fr g -> Prod fr h
polyProd ::  -- pure
  Implic (Prod fr U1) => (forall a. f a) -> Prod fr f
```

They are both also functor, foldable, traversable, etc
using the same generalization from `* -> *` to `(* -> *) -> *`.

TODO discuss `Implic`, which is implemented via `FragPop_NonDet`

# Internals
[sec:internals]: #internals

This section explains the implementation of the `frag` package.

It takes for granted a significant familiarity with GHC internals.
This `README` file is usually accompanied by a `ghc-internals` file,
to which the interested reader should refer.

## Frag semantics
[sec:internals-semantics]: #frag-semantics

Informally, the terms inhabiting `Frag b` denote multisets.
That would imply that `Frag b` denotes the free abelian group over whatever `b` denotes.
However, `Frag b` cannot itself be a group;
it does not even have a binary operator.
What is going on?
How sound is that informal notion?

Any term inhabiting `Frag b` is equivalent to a pair of a *root* and an *extension*.
The extension is a possibly empty sequence of signed tallies,
and the root is another term inhabiting `Frag b`.
We usually assume that the root, which viewed as a pair itself, has an empty extension --
so the root is either `'Nil` or a type variable (including flattening variables).
There is a crucial reason that it is safe to assume that!
Extensions form a monoid
and therefore the functor that pairs an X with an extension
is a ("writer") monad over X:
its unit pairs an X with the empty extension,
and its join merely combines the two extensions.

This extension monoid is moreover the free abelian group over the terms inhabiting `b`.
(See [formal sum (Wikipedia)](https://en.wikipedia.org/wiki/Free_abelian_group#Integer_functions_and_formal_sums).)
The unit is the empty sequence of tallies,
the group operator is concatenation --
i.e. arithmetic over *signed `b`-ornamented unary numerals*, i.e. multiset union, which is associative and commutative --
and the inverse function flips the sign of each tally.

The equational theory of `Frag b` is determined by its equivalence to
the "writer" monad with the free abelian group of `b`-inhabitants as its "output"
and `Frag b`-inhabitants as its carrier (i.e. its X).
And in a fully *grounded* inhabitant of `Frag b`
(no type variables (including function application), impredicativity?, etc?),
the root is `'Nil`,
so the term is the extension, which is a multiset.
Thus, the informal notion that frags denote multsets seems reasonable.

TODO Call out the canonical(?) action of the extension group on terms of `Frag b`?

## Rules
[sec:internals-rules]: #rules

The plugin grants `Frag` and the related type families the intended semantics.
This section specifies how.

The following rules constitute
a high-level specification of the semantics of the `frag` library API as a rewrite relation `⟶`.
I use the same symbol for rewriting types, rewriting constraints, and rewriting evidence.

I use some abbreviations.

  * `:+-` stands consistently for either `:+` or `:-` within an instance of a rule,
    and `:-+` stands for the other tally.

  * We use the simple pattern `fr ? :+- a` to mean a complicated thing.
    For example, the following rule template would mean
    "if the argument of `X` has an extension including a tally for `a` *any where in it* such that the antecedant `ante` is satisfied, remove that tally."

    ```haskell
    ante
    --------------------
    X (fr ? :+- a)   ⟶   X fr
    ```

    If `a` occurs else where in the consequent,
    then the antecedent implicitly includes the corresponding equalities.

    I also use `fr@(x ? :+- a)` to refer to the actual frag as `fr`.

  * I use the pattern `FragNE a ? fr` in a similar way,
    since the plugin reorders nestings of `FragNE`.

  * `EXT(r,e)` stands for a frag root and extension pair.
    Note that `EXT('Nil,z)` is a manifest signed unary numeral `z` when the basis is `()`.

  * `NEGATE(e)` stands for the same extension but with all the tallies negated.

### Constructors

These two rules use the key semantics of abelian groups in order to
canonicalize the syntactic representation of a frag extension.

```haskell
b < a according to ORDER_FRAGILE
-------------------- [tally-commute]
fr :+- a :+- b   ⟶   fr :+- b :+- a

-------------------- [tally-inverse]
fr :+- a :-+ a   ⟶   fr
```

Recall the two orders on type representations from [Universes][sec:frag-universes], `ORDER_FRAGILE` and `ORDER_STABLE`.

  * The `ORDER_FRAGILE` order is total but not preserved by renaming and/or substitution.

  * The `ORDER_STABLE` order is partial but is preserved by renaming and substituion.

### Observers

```haskell
-------------------- [FragEQ-Nil]
FragEQ a 'Nil   ⟶   'Nil

-------------------- [FragEQ-Z]
FragEQ a (fr :: Frag ())   ⟶   fr

-------------------- [FragEQ-tally-equal]
FragEQ a (fr ? :+- a)   ⟶   (FragEQ a fr) :+- '()

a /~ b
-------------------- [FragEQ-tally-apart]
FragEQ a (fr ? :+- b)   ⟶   FragEQ a fr
```

```haskell
-------------------- [FragLT-Nil]
FragLT a 'Nil   ⟶   'Nil

-------------------- [FragLT-Z]
FragLT a (fr :: Frag ())   ⟶   'Nil

a ≤ b according to ORDER_STABLE
-------------------- [FragLT-tally-≤]
FragLT a (fr ? :+- b)   ⟶   FragLT a fr

b < a according to ORDER_STABLE
-------------------- [FragLT-tally->]
FragLT a (fr ? :+- b)   ⟶   (FragLT a fr) :+ '()
```

### Hybrids

`FragNE` is an `filter`-like operation, so it cannot be considered solely as an observer.
In particular, the rules for each observer must additionally specify how that observer acts on `FragNE`.
Note that the rules for `FragNE` itself do so.

```haskell
-------------------- [FragNE-Nil]
FragNE a 'Nil   ⟶   'Nil

-------------------- [FragNE-Z]
FragNE a (fr :: Frag ())   ⟶   'Nil

-------------------- [FragNE-tally-equal]
FragNE a (fr ? :+- a)   ⟶   FragNE a fr

a /~ b
-------------------- [FragNE-tally-apart]
FragNE a (fr ? :+- a)   ⟶   (FragNE a fr) :+- a
```

```haskell
-------------------- [FragNE-FragNE-equal]
FragNE a (FragNE a fr)   ⟶   FragNE a fr

b < a according to ORDER_FRAGILE
-------------------- [FragNE-FragNE->]
FragNE a (FragNE b fr)   ⟶   FragNE b (FragNE a fr)
```

```haskell
-------------------- [FragEQ-FragNE-equal]
FragEQ a (FragNE a ? fr)   ⟶   'Nil

a /~ b
-------------------- [FragEQ-FragNE-apart]
FragEQ a (FragNE b ? fr)   ⟶   FragEQ a fr
```

```haskell
a ≤ b according to ORDER_STABLE
-------------------- [FragLT-FragNE-≤]
FragLT a (FragNE b ? fr)   ⟶   FragLT a fr
```

### Predicates

The rules for `SetFrag` and the rules for `EqFrag 'Nil` are very similar,
since both predicates are only constraining every multiplicity in the frag,
`SetFrag` to `0 ≤ p ≤ 1` and `EqFrag 'Nil` to `0 = p`.

```haskell
-------------------- [SetFrag-Nil]
SetFrag 'Nil   ⟶   ()

-------------------- [SetFrag-one]
SetFrag ('Nil :+ a)   ⟶   ()

SetFrag fr
-------------------- [SetFrag-FragNE]
SetFrag (FragNE a fr)   ⟶   ()

a /~ '()
-------------------- [SetFrag-tally]
SetFrag (fr ? :+- a)   ⟶
  ( SetFrag (FragNE a fr) , SetFrag (FragEQ a fr :+- '()) )
```

```haskell
-------------------- [Empty-Nil]
EqFrag 'Nil fr   ⟶   ()

a /~ '()
-------------------- [Empty-tally]
EqFrag 'Nil (fr ? :+- a)   ⟶
  ( EqFrag 'Nil (FragNE a fr) , EqFrag 'Nil (FragEQ a fr :+- '()) )
```

```haskell
-------------------- [KnownFragCard-Nil]
KnownFragCard 'Nil   ⟶   0

-------------------- [KnownFragCard-tally]
KnownFragCard (fr :+- a)   ⟶   KnownFragCard fr +- 1
```

### Relations

```haskell
-------------------- [Eq-tally]
EqFrag (frL :+- a) frR   ⟶   EqFrag frL (frR :-+ a)

r /~ 'Nil
-------------------- [Eq-difference]
EqFrag r EXT(r,e)   ⟶   EqFrag 'Nil EXT('Nil,e)

r /~ 'Nil
-------------------- [Eq-swap]
EqFrag r EXT('Nil,e)   ⟶   EqFrag 'Nil EXT(r,NEGATE(e))
```

### Known multiplicities

```haskell
EqFrag (FragEQ a r) EXT('Nil,z)
-------------------- [FragEQ-multiplicity]
FragEQ a EXT(r,e)   ⟶   EXT( FragEQ a EXT('Nil,e) ,z)

EqFrag (FragEQ a r) 'Nil
-------------------- [FragNE-multiplicity]
FragNE a EXT(r,e)   ⟶   EXT(r,e)
```

Applying `[FragNE-multiplicity]` in the argument of `SetFrag` and `EqFrag 'Nil` might lead to some redundant constraints.

### Improvement

The above rules specify the core semantics.
As usual, we omitted the rules for explicitly recognizing contradictions.
We do however list the following admissible rules for deriving equalities and/or apartnesses.

If
  * a basis element `a` must have a positive multiplicity `z` in a frag `EXT('Nil,e)`
  * `e` splits into `neg` and `pos` by sign
  * the total multiplicity of `pos` is `z`
then
  * every basis element in `pos` must be equivalent to `a`
  * every basis element in `neg` must be apart from `a`

```haskell
fr is stuck
e is stuck
e splits into (neg,pos) by sign
z = card(pos)
-------------------- [Empty-FragEQ-Nil-improve-pos]
    EqFrag 'Nil fr@(EXT(FragEQ a EXT('Nil,e),NEGATE(z)))
  ⟶
    ( ∀b in neg. a /~ b , ∀b in pos. a ~ b )
```

We have the same rule mutatis mutandi when the required multiplicity `z` is negative.

```haskell
fr is stuck
e is stuck
e splits into (neg,pos) by sign
z = card(neg)
-------------------- [Empty-FragEQ-Nil-improve-neg]
    EqFrag 'Nil fr@(EXT(FragEQ a EXT('Nil,e),NEGATE(z)))
  ⟶
    ( ∀b in neg. a ~ b , ∀b in pos. a /~ b )
```

If
  * a frag `EXT('Nil,e) :+ a` must be empty
  * `e` splits into `neg` and `pos` by sign
  * `a` occurs in the frag at least as many times
    as all the elements in `neg` that are not certainly apart from `a`
then
  * all those elements must unify with `a`

```haskell
fr is stuck
e splits into (neg,pos) by sign
neg further splits into (u,d) by whether a /~ b is decided
a occurs manifestly in fr at least CARD(NEGATE(u)) many times
-------------------- [EqFrag-Nil-Nil-improve-pos]
    EqFrag 'Nil fr@(EXT('Nil,e) ? :+ a)
  ⟶
    ( EqFrag 'Nil EXT(EXT('Nil,pos),d) :+ a :+ CARD(u)*a , ∀b in u. a ~ b )
```

We have the same rule mutatis mutandi when `a` has negative apparent multiplicity.

```haskell
fr is stuck
e splits into (neg,pos) by sign
pos further splits into (u,d) by whether a /~ b is decided
a occurs manifestly in fr at least CARD(u) many times
-------------------- [EqFrag-Nil-Nil-improve-neg]
    EqFrag 'Nil fr@(EXT('Nil,e) ? :- a)
  ⟶
    ( EqFrag 'Nil EXT(EXT('Nil,neg),d) :- a :+ CARD(u)*a , ∀b in u. a ~ b )
```

If
  * the multiplicity of an element `b` in a frag `EXT('Nil,e)` must be `0-z` or `1-z`
  * ie `0 ≤ ( e(b) + z ) ≤ 1`
  * `e` splits into `neg` and `pos` by sign
  * an element `a` either has
    * negative apparent multiplicity in `e`
	  and `z` is too positive compared to the total multiplicity of `neg` excluding `a`
    * positive apparent multiplicity in `e`
	  and `z` is too negative compared to the total multiplicity of `pos` excluding `a`
then
  * `a` and `b` must unify

```haskell
z is CARD(outer)
e splits into (neg,pos) by sign
k is e(a)
  (k < 0 && z - (CARD(neg) - k) > 1)
||
  (k > 0 && z + (CARD(pos) - k) < 0)
-------------------- [SetFrag-FragEQ-improve-equal]
    SetFrag EXT(FragEQ b EXT('Nil,e@(_ ? :+- a)),outer)
  ⟶
    ( SetFrag EXT(FragEQ b EXT('Nil,e :-+ CARD(k)*a),EXT(outer,k)) , a ~ b )
```

We have a similar rule that recognizes when `a` must be apart from `b`;
ie when the additional multiplicity if `a` were equivalent to `b` would certainly overshoot `z`.

```haskell
z is CARD(outer)
e splits into (neg,pos) by sign
k is e(a)
  (k < 0 && z + k + CARD(pos) < 0)
||
  (k > 0 && z + k - CARD(neg) > 1)
-------------------- [SetFrag-FragEQ-improve-apart]
    SetFrag EXT(FragEQ b EXT('Nil,e@(_ ? :+- a)),outer)
  ⟶
    ( SetFrag EXT(FragEQ b EXT('Nil,e :-+ CARD(k)*a),outer) , a /~ b )
```

### Multiplicity Table and Apartness Table

TODO elaborate

In the above rules,
multiplicities occur as antecedents such as `EqFrag (FragEQ a r) EXT('Nil,z)`.
Read this as "the plugin has determined that the multiplicity of the basis element `a` in the root `r` is the integer `z`".
In order to check these, the plugin maintains a table of known multiplicities as it simplifies constraints.
Whenever it adds a constraint to its own inert set,
if that constraint has the right form,
it updates the table accordingly.

We similarly maintain a table for given constraints that ensure two types are apart.
This table can affect the antecedents of `[EqFrag-Nil-Nil-improve-neg]`, for example.

## Normalization
[sec:internals-normalization]: #normalization

TODO what the plugin could do without normalizing

TODO what the plugin can do with normalizing

TODO what the plugin cannot do even with normalizing

TODO how we normalize

## Floating equivalences
[sec:internals-floating-eqs]: #floating-eqs

Given `SetFrag` and `Apart` constraints need to prevent GHC from floating Wanted `~` constraints out of implications;
see the `ghc-internals` file for the general motivation.
This is why these classes are implemented as degenerate `~` constraints intsead methodless classes.

Floating equalities is also why the plugin uses the same rules GHC does
whenever choosing between two equivalent variables.
By orienting `x ~ y` instead of `y ~ x` based on various qualities of the two
(eg relative level, flavour, etc)
the resulting substitutions may enable additional equalities to float.

## Flattening
[sec:internals-flattening]: #flattening

It took me a long time to introduce `EqFrag` instead of using `~` directly at kind `Frag k`.
However, it's a syntactic overhead worth paying.
The basic challenge is that we use `:+` and `:-` type families as frag syntax.
So GHC sees frags as type family applications,
which means it flattens them to a skolem.
For example, GHC (temporarily) rewrites an equivalence `tv2 ~ tv1 :+ Int` to `(tv2 ~ fsk,tv :+ Int ~ fsk)`.
This has the unfortunate consequence that GHC may re-orient to `fsk ~ tv2`,
depending on particular details of `fsk` that the plugin cannot control.
Note that this will replace occurrences of `tv1` (specifically any `tv1 :+ Int`) with `tv2`,
which may spuriously block floating if `tv2` has a deeper level than `tv1`.
(I'm not totally sure this spurious blocking can currently happen,
because GHC's heuristics are currently too conservative for it to matter anyway.
I think it will eventually be an issue,
and it seems a crucial aspect of the GHC constraint solver architecture --
so I've gone ahead an addressed it at some complexity cost.)

If I were to properly formalize the plugin's constraint solving algorithm,
I would carefully consider the choice I've made to normalize frags with respect to commutativity *as a part of* applying the frag-specific inert substitution.

TODO challenges from <https://gitlab.haskell.org/ghc/ghc/issues/15147> unflattened Wanteds
