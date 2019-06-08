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
      * [Optics][sec:motley-optics]
  * [Internals][sec:internals]
    * [Frag semantics][sec:internals-semantics]
    * [Rules][sec:internals-rules]
    * [Normalization][sec:internals-normalization]
    * [Derived equivalences][sec:internals-derived-eqs]
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
to distill a proper GHC patch out of it for /row polymorphism/.
I've learned a lot, and there's thankfully no end in sight on that front.
And of the several from-scratch iterations I've done in private,
I'm delighted to finally share one that feels promising!

This repository was, is, and will remain a hobby project.
My work on it will continue to be bursty.
I'm excited to cooperate with you!
But my bandwidth is limited :(

## About this documentation

We must maximize how accurate, available, and approachable they feel
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
and a typechecker plugin implements its equational theory.

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

TODO forward reference to [`motley` products][sec:motley-products].

TODO sentence transitioning to next section

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

The `FragLT e fr` application denotes the total multicplity
of all elements `x` in `fr` such that `x < e`.
That `<` sign refers to a strict partial order on types that we call `ORDER_STABLE`.
How exactly it relates types is an implementation detail of GHC and the plugin.
It has a few key properties that make it safe for our use here.

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
data FragRep :: Frag b -> b -> * where
  MkFragRep ::
      (FragEQ e fr ~ ('Nil :+ '()),KnownFragCard (FragLT e fr))
	=>
	  FragRep fr e

testEquality_FragRep ::
  SetFrag fr ~ '() => FragRep fr x -> FragRep fr y -> Maybe (x :~: y)
```

Note the set constraint in the type of `testEquality_FragRep`:
this coercion is only safe if all of the multiplicities in `fr` are non-negative.
`SetFrag` is all we have at hand,
but positive multiplicities greater than `1` would be fine here.

There are other useful functions over `FragRep`.
For example, if `y` is the minimum of `fr :+ y`,
then we can embed `FragRep fr x` into `FragRep (fr :+ y) x`.
(Operationaly, this increments the integer in the `KnownFragCard` dictionary.)

```haskell
widenFragRepByMin :: (FragLT y fr ~ 'Nil) => proxyy y -> FragRep fr x -> FragRep (fr :+ y) x
```

TODO discuss all `FragRep` axia here as part of <https://github.com/nfrisby/frags/issues/39>

## Nominal view
[sec:frag-nominal-view]: #nominal-view

TODO

```haskell
type family FragPop_NonDet (fr :: Frag k) :: MaybeFragPop k where {}

type family FragPush (mpop :: MaybeFragPop k) :: Frag k where {}
```

## Auxiliaries
[sec:frag-auxiliaries]: #auxiliaries

If only because of implementation details,
the following types are relevant to the user.

### Frag masking

The library provides the following elimination form.

```haskell
type family FragNE (e :: b) (fr :: Frag b) :: Frag b where {}
```

The multiciplities of `FragNE e fr` agree with those of `fr` except on `e`,
which has a multiplicity of `0`.
Thus, `FragNE e` removes `e` from `fr`'s *support*,
the *set* of elements with non-zero multiplicities.

(Observation: A set frag is equivalent to its own support.)

### Apartness constraints

TODO motivate and define

# `motley` API
[sec:motley-api]: #motley-api

The `motley` library uses the frag polymorphism and frag universes of the `frag` library
to define n-ary type-indexed sums and products.

## Sums
[sec:motley-sums]: #sums

TODO

```haskell
data Sum :: Frag b -> (b -> *) -> * where
  MkSum :: !(FragRep fr e) -> f e -> Sum fr f
```

## Products
[sec:motley-products]: #products

TODO

```haskell
data Prod :: Frag b -> (b -> *) -> * where
  MkCons ::
      (FragLT e fr ~ 'Nil,FragEQ e fr ~ 'Nil)
	=>
	  !(Prod fr f) -> f e -> Prod (fr :+ e) f
  MkNil :: Prod 'Nil f
```

TODO mention <https://github.com/nfrisby/frags/issues/9> flat Prod

## Combinators
[sec:motley-combinators]: #combinators 

TODO

```haskell
updateSum :: Prod fr (f ~> g) -> Sum fr f -> Sum fr g
updateProd :: Sum fr (Compose Endo f) -> Prod fr f -> Prod fr f
```

# Optics
[sec:motley-optics]: #optics

TODO

```haskell
opticSum ::
    ( SetFrag fr ~ '()
    , FragEQ x fr ~ 'Nil,KnownFragCard (FragLT x fr)
	, FragEQ y fr ~ 'Nil,KnownFragCard (FragLT y fr)
	)
  =>
    Prism.Prism (Sum (fr :+ x) f) (Sum (fr :+ y) f) (f x) (f y)
```

```haskell
opticProd ::
    (
	  FragEQ x fr ~ 'Nil,KnownFragCard (FragLTx fr)
	,
	  FragEQ y fr ~ 'Nil,KnownFragCard (FragLT y fr)
    )
  =>
    Lens.Lens (Prod (fr :+ x) f) (Prod (fr :+ y) f) (f x) (f y)
```

# Internals
[sec:internals]: #internals

This section explains the imlementation of the `frag` package.

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
    We use the simple pattern `fr ? :+- a` to mean a complicated thing.
    For example, the following rule template would mean
    "if the argument of `X` has an extension including a tally for `a` *any where in it* such that `ante` is satisfied, remove that tally."

    ```haskell
    ante
    --------------------
    X (fr ? :+- a)   ⟶   X fr
    ```

    If `a` occurs else where in the consequent,
	then the antecedent implicits includes the corresponding equalities.

    I also use `fr@(x ? :+- a)` to refer to the actual frag as `fr`.

  * I use the pattern `FragNE a ? fr` in a similar way.

  * `EXT(r,e)` stands for a frag root and extension pair.
    Note that `EXT('Nil,z)` is a manifest signed unary numeral `i` when the basis is `()`.

  * `NEGATE(e)` stands for the same extension but with all the tallies negated.

### Constructors

These two rules use the key semantics of abelian groups in order to
canonicalize the syntactic representation of a frag extension.

```haskell
b < a according to FRAGILE
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
since predicates both are only constraining every multiplicity in the frag,
`SetFrag` to `0 ≤ p ≤ 1` and `EqFrag 'Nil` to `0 = p`.

```haskell
-------------------- [SetFrag-Nil]
SetFrag 'Nil   ⟶   ()

-------------------- [SetFrag-one]
SetFrag ('Nil :+ a)   ⟶   ()

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

```haskell
e is stuck
e splits into (neg,pos) by sign
z = card(neg)
-------------------- [Empty-FragEQ-Nil-improve-neg]
    EqFrag 'Nil EXT(FragEQ a EXT('Nil,e),z)
  ⟶
    ( ∀b in neg. a ~ b , ∀b in pos. a /~ b )

e is stuck
e splits into (neg,pos) by sign
z = card(pos)
-------------------- [Empty-FragEQ-Nil-improve-pos]
    EqFrag 'Nil EXT(FragEQ a EXT('Nil,e),NEGATE(z))
  ⟶
    ( ∀b in neg. a /~ b , ∀b in pos. a ~ b )
```

```haskell
fr is stuck
e splits into (neg,pos) by sign
neg further splits into (u,d) by whether a /~ b is decided
a occurs manifestly in fr at least CARD(NEGATE(u)) many times
-------------------- [EqFrag-Nil-Nil-improve-pos]
    EqFrag 'Nil fr@(EXT('Nil,e) ? :+ a)
  ⟶
    ( EqFrag 'Nil EXT(EXT('Nil,pos),d) :+ a :+ CARD(u)*a , ∀b in u. a ~ b )

fr is stuck
e splits into (neg,pos) by sign
pos further splits into (u,d) by whether a /~ b is decided
a occurs manifestly in fr at least CARD(u) many times
-------------------- [EqFrag-Nil-Nil-improve-neg]
    EqFrag 'Nil fr@(EXT('Nil,e) ? :- a)
  ⟶
    ( EqFrag 'Nil EXT(EXT('Nil,neg),d) :- a :+ CARD(u)*a , ∀b in u. a ~ b )
```

TODO rules for deriving eqs and aps from `SetFrag`

TODO the tracking of intervals in inert set cache

## Normalization
[sec:internals-normalization]: #normalization

TODO what the plugin could do without normalizing

TODO what the plugin can do with normalizing

TODO what the plugin cannot do even with normalizing

TODO how we normalize

## Floating equivalences
[sec:internals-floating-eqs]: #floating-eqs

TODO why `SetFrag` and `Apart` need to block them,

TODO why the `~ '()` workaround does.

TODO refer to <https://ghc.haskell.org/trac/ghc/wiki/FloatMoreEqs2018>

## Flattening
[sec:internals-flattening]: #flattening

TODO GHC's flattening, especially avoiding loops reorienting frag equivalences

TODO unflattening via the frag substitution

TODO challenges from <https://gitlab.haskell.org/ghc/ghc/issues/15147> unflattened Wanteds
