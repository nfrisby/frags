# Documentation for `frag` and `motley`

This file always contains the latest official documentation
for the `frag` and `motley` libraries.

# Table of Contents

  * [Meta][sec:meta]
  * [How to Use][sec:how-to-use]
    * [Installation][sec:how-to-use-installation]
    * [Purpose][sec:how-to-use-purpose]
    * [Tutorial][sec:how-to-use-tutorial]
  * [`frag` API][sec:frag-api]
      * [Introduction forms and equivalence][sec:frag-intro-and-eq]
      * [Integers][sec:frag-integers]
      * [Sets][sec:frag-sets]
      * [Frag polymorphism][sec:frag-polymorphism]
      * [Universes][sec:frag-universes]
      * [Nominal view][sec:frag-nominal-view]
      * [Auxiliaries][sec:frag-auxiliaries]
  * [`motley` API][sec:motley-api]
      * [Places][sec:motley-places]
      * [Sums][sec:motley-sums]
      * [Products][sec:motley-products]
      * [Combinators][sec:motley-combinators]
  * [Internals][sec:internals]
    * [Frag semantics][sec:internals-semantics]
    * [Rules][sec:internals-rules]
    * [Normalization][sec:internals-normalization]
    * [Floating equivalences][sec:internals-floating-eqs]
    * [Flattening][sec:internals-flattening]
    * [Congruence Closure][sec:internals-congruence-closure]

# Meta
[sec:meta]: #meta

## Readiness

These packages are currently *not even alpha* quality.
Use at your own risk.
I'm releasing to pique interest and to find collaborators! :)

The license is BSD3.
(I'm flexible on this.
If users eventually need something else,
please reach out.)

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
we'd like to keep the higher-level discussions there
and dig into the details on the PRs.

## Acknowledgements

The GHC developer community has been very helpful and encouraging
over the few years we've iterated on this project.
There are too many to list them all, but
Simon Peyton Jones,
Adam Gundry,
Richard Eisenberg,
Iavor Diatchki,
E.Z. Yang,
Jan van Brügge,
and AntC (?)
have given several answers, conversation, and encouragement that helped a lot.

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

# How to Use
[sec:how-to-use]: #how-to-use

## Installation
[sec:how-to-use-installation]: #installation

The most recent and stable versions will be on Hackage and available on the `master` branch.
So typical use is:
  * add `frag` and `motley` to the `build-depends` field of your `.cabal` file (or equivalent)
    * handle version constraints as you wish;
      these Hackage releases will follow the [Haskell Package Versioning Policy](https://pvp.haskell.org/)
  * import `Data.Motley`, likely also `Data.Frag`, and maybe some of the others (eg `Data.Implic`) in your modules
  * pass `-dcore-lint -fplugin=Data.Frag.Plugin` to `ghc`
  * likely also pass `-fconstraint-solver-iterations=N` where `N` is around 20 or so --
    if 50 iterations isn't enough for your use, you've almost certainly found a bug

I personally favor `OPTIONS_GHC` pragmas in my module headers.

```haskell
{-# OPTIONS_GHC -dcore-lint -fplugin=Data.Frag.Plugin #-}

{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}
```

But you can also put these in the `.cabal` file's `ghc-options` field, for example.

If you're working with the source,
see the adjacent `docs/DEVELOPING.md` file.

Last tip: If the plugin seems to be failing on really simple uses,
the first step is always to confirm that the `-fplugin` and `-dcore-lint` options are set!

## Library Interface

See the Haddock and also the [`frag`][sec:frag-api] and [`motley`][sec:motley-api] sections of this document.

## Purpose
[sec:how-to-use-purpose]: #purpose

The long-term goal of this project is a GHC typechecker plugin that provides row polymorphism etc.
It's not all the way to row polymorphism yet,
but it has reached an interesting milestone.

Some broadly suggestive use-cases:

  * In general, it provides *strucural typing*, such as used for [OCaml's *immediate objects*](https://caml.inria.fr/pub/docs/manual-ocaml/objectexamples.html)
    -- note that this is just the immediate objects, not the classes, inheritance, etc.
	(TODO applicable to https://www.well-typed.com/blog/2018/03/oop-in-haskell/ ?)

  * The row types and those indexed by them are *extensible*;
    they should be able to provide a (partial?) alternative to [*Trees that Grow*](https://www.microsoft.com/en-us/research/publication/trees-that-grow/),
	[*Data types à la carte*](http://www.staff.science.uu.nl/~swier004/publications/2008-jfp.pdf), etc.

  * Any sums (eg `Either`), especially nested, where the summands are unique and the order does not matter.
    For example, the arguments to `serve` in the `servant-server` package.
    (The order matters for overlapping routes, but there is a middle-ground to consider.)
    For example -- though it's rarely recommended practice -- types tracking which synchronous exceptions can be thrown.

  * More generally, structural and extensible types are a perfect fit for algebraic effects libraries,
    in which a sum tracks the available/used effects.

  * Any tuples, nested or not, where the components are unique and the order does not matter.
    For example, the `QueryParam` and `Capture` corresponding arguments to handlers in the argument to `serve` in the `servant-server` package.
    (They are not necessarily uniquely named, but probably should be.)
    For example, columnar/tabular data (SQL, CSV, data frames, etc), especially if columns are to be freely added/removed/ignored during processing.

  * Any sums or tuples where "sub-sums" or "sub-tuples" are of interest.
    For example, the `Step` type from the `vector` package has `Done`, `Skip s`, and `Yield a s` constructors.
    It might be useful to freely use subsums such as just `Done` and `Yield` (no `filter`), just `Skip` and `Yield` (`filter`able infinite streams), etc.
    And a row polymorphic `mapS` function could be applied to any subsum that has `Yield`s.
    This can make library's interface much more flexible for the user.

  * More generally, structural and extensible types enable such mix-and-match composition of sums and products,
    especially from an a priori fixed set.
	For example, a program might define a set of command-line argument parsers and descriptions to be composed when defining an interface that involves several subcommands.
	For example, a library might provide `abbrvnat`-style renderings of products corresponding to BibTeX entries,
	postal service-compliant renderings of addresses,
	Chicago Manual of Style-compliant renderings of formal names with honorifics, suffices, and so on,
	RFC-compliant renderings of times/durations,
	etc,
	as long as the given produts have *at least* the required fields, maybe more.
	The library would provide a set of data type sfor the fields it cares about,
	and the user could compose those -- as well as others -- into products however they desire.

  * TODO JSON schema?

## Tutorial
[sec:how-to-use-tutorial]: #tutorial

The [`frag` API][sec:frag-api] and [`motley` API][sec:motley-api] sections cover a lot of ground
and do so rather quickly.
This section covers less ground more slowly.
You can also find skeletons of use-cases in the `motley/test/*` directory and the `examples-motley` package.

The project documentation mostly takes for granted that row/frag polymorphism is useful.
This section will demonstrate in passing some of its utility,
but will be emphasizing *how* to use it more so than *why*.

Suppose we're interacting with a database,
and that its entity-relationship diagram involves humans and dogs.
A Haskell interface to the database would likely include separate ID types for each kind of entity,
since human #4 and dog #4 should not be confounded.
Let's also suppose the database tracks first name and age,
which are properties both of humans and also of dogs.

```haskell
newtype HumanId = MkHumanId{humanId :: Int}
  deriving (Eq,Ord,Show)
newtype DogId = MkDogId{dogId :: Int}
  deriving (Eq,Ord,Show)

newtype FirstName = MkFirstName{firstName :: Text}
  deriving (Eq,Ord,Show)
newtype Age = MkAgeDays{ageDays :: Int}
  deriving (Eq,Ord,Show)
```

The database has property tables for humans and for dogs
and a link table indicating who is whose best friend.

```haskell
type HumanTable = 'Nil :+ HumanId :+ FirstName :+ Age
type DogTable = 'Nil :+ DogId :+ FirstName :+ Age
type BestFriendTable = 'Nil :+ HumanId :+ DogId
```

These type are our first frags!
The `'Nil` type is the empty frag,
and the `:+` family adds the specified basis element.
It associates to the left,
so we're starting with the empty frag and adding `HumanId`, `FirstName`, etc.
Since each basis element inhabits the `Type` kind,
the frags inhabit the `Frag Type` kind.
These are *set frags* because every possible inhabitant of `Type` occurs either 0 or 1 times in each frag.
In other words, for each frag, it is true that all basis element multiplicities in that frag are 0 or 1.

Suppose human #1 is about 41 years old and named Danai.

```haskell
extI p x = ext p (Identity x)

danai_ = nil `extI` MkHumanId 1 `extI` MkAgeDays 15096 `extI` MkFirstName "Danai"
```

GHC infers that `danai_ :: Prod ('Nil :+ HumanId :+ Age :+ FirstName) Identity`.
The `Identity` type and constructor are from the `base` package's `Data.Functor.Identity` module.
The `nil` and `ext` functions come from the `motley` package.
`nil` is the empty `Prod`uct, and `ext` extends a product by including an additional factor.
Compare `nil` to `'Nil`' and `ext` to `:+`.

The core underlying idea of frags is that the order of basis elements does not matter.
Therefore, `danai_` inhabits `Prod HumanTable Identity`, even though its inferred type has the (same) basis elements in a different order!

```haskell
danai :: Prod HumanTable Identity
danai = danai_
```

Danai has a puppy.

```haskell
scout :: Prod DogTable Identity
scout = nil `extI` MkAgeDays 65 `extI` MkFirstName "Scout" `extI` MkDogID 1
   -- note again: GHC with the plugin is happy to permute the factors

prjI p = runIdentity (prj p)

danai_scout :: Prod BestFriendTable Identity
danai_scout = nil `extI` prjI scout `extI` (prjI danai :: HumanId)
```

The `prj` function projects a factor out of a product;
so the Haskell source expression `prjI danai` evaluates to `MkHumanId 1`.
And that same source expression `prjI danai` also evaluates `MkFirstName "Danai"` --
the returned value is determined by both the argument and the demanded type.

We also see frag polymorphism in action in `danai_scout`.
Why didn't we have to write `prjI scout :: DogId`?
It's because GHC knows that `BestFriendTable ~ ('Nil :+ HumanId :+ DogId)`,
and we've given it a `HumanId`,
so the only thing left for us to have given it is a `DogId`.
More specifically, the code incurs the constraint `BestFriendTable ~ ('Nil :+ alpha :+ HumanId)`
and the plugin helps GHC simplify that constraint to `alpha ~ DogId`.
This is very similar to the inferences at the core of traditional row polymorhpism.

We could also have written ``nil `extI` (prjI scout :: DogId) `extI` prjI danai``,
and GHC would have made the symmetric inference.
Unfortunately, we cannot just write ``nil `extI` prjI scout `extI` prjI danai``;
with its current implementation, the plugin and GHC together see this as amibiguous,
the same way that `show (read s)` is ambiguous.
We haven't given GHC enough information to know which factor should be the human and which should be the dog.
The answer still seems obvious to the human coder,
but that's because we're intuitively doing a backtracking search of sorts,
and the GHC typechecker does not backtrack/make guesses.
(FYI, I think the plugin could eventually handle this with no annotations;
see <https://github.com/nfrisby/frags/issues/42> and consider for example `IdOf Human` and `IdOf Dog`.)

So now we have three values, each of which could be inserted as a row into one of the database tables:
`danai`, `scout`, and `danai_scout`.

```haskell
*Main> danai
{(Identity (MkHumanId 1)) (Identity (MkAgeDays 15096)) (Identity (MkFirstName "Danai"))}
*Main> scout
{(Identity (MkDogId 1)) (Identity (MkAgeDays 65)) (Identity (MkFirstName "Scout"))}
*Main> danai_scout
{(Identity (MkDogId 1)) (Identity (MkHumanId 1))}
```

Why did `danai_scout` print as `{(Identity (MkDogId 1)) (Identity (MkHumanId 1))}`
instead of as `{(Identity (MkHumanId 1)) (Identity (MkDogId 1))}`?
By using internal implementation details of GHC,
the plugin establishes a total ordering on *ground types*,
ie "completely monomorphic" types that involve no type variables.
For the same version of GHC and the plugin, this order will be entirely consistent.
But the actual pairwise orderings should be considered *unpredictable*,
and moreover different versions of GHC/the plugin may use different orderings.
In particular, the `Prod` type uses the ordering to sort its underlying linked list of ascending factors.
In other words, the dog ID was printed before the human ID because
-- apparently -- GHC determined `DogID < HumanID`.

The types so far have been simple because there were not any type variables.
Let's dig into the types of `ext` and `prj`, which are very polymorphic.

```haskell
*Main> :info ext
ext ::
  forall k (a :: k) (p :: Frag k) (f :: k -> *).
  (FragEQ a p ~ 'Nil, KnownFragCard (FragLT a p)) =>
  Prod p f -> f a -> Prod (p :+ a) f
*Main> :info prj
prj ::
  forall k (a :: k) (p :: Frag k) (f :: k -> *).
  (FragEQ a p ~ 'Nil, KnownFragCard (FragLT a p)) =>
  Prod (p :+ a) f -> f a
```

If you ignore the contexts (the part before `=>`),
then the types are `Prod p f -> f a -> Prod (p :+ a) f` and `Prod (p :+ a f) -> f a`,
which hopefully seem intuitive at this point.
(We've only used `f ~ Identity` in our examples,
but the `motley` types work for other `f` types too.
[*Higher Kinded Data*](https://reasonablypolymorphic.com/blog/higher-kinded-data/) has become a popular moniker for this parameter.)

Let's consider the shared context of `ext` and `prj` now:
`(FragEQ a p ~ 'Nil, KnownFragCard (FragLT a p))`.

```haskell
*Main> :info FragEQ
type family FragEQ (a :: k) (fr :: Frag k) :: Frag ()
*Main> :info FragLT
type family FragLT (a :: k) (fr :: Frag k) :: Frag ()
```

First thing to notice: `Frag ()` seems important.
What is that kind?
It's the frags in which the basis elements inhabit the `()` data kind.
In other words, its the frags that have only one basis element.
And here's the big reveal: frags are not just sets,
they are multisets and moreover the multiplicities can be negative.
Therefore, `Frag ()` is like a data kind for integers.
For example, 0 is `'Nil` and negative 2 is `'Nil :- '() :- '()` --
note that I wrote `:-` and not `:+`.

So, reading `Frag ()` as "integer", `FragEQ a fr` and `FragLT a fr` are counts.
In fact, `FragEQ a fr` is the multiplicity of the basis element `a` in the frag `fr`.
The `FragEQ a p ~ 'Nil` constraints on `ext` and `prj` are just saying that `a` is not in `p`: it has 0 multiplicity.
The consequences are similar to the `p Lacks a` constraint from traditional row polymorphism.

Whereas `FragEQ a p` is the total multiplicity of basis elements in `p` that are equivalent to `a`,
`FragLT a p` is the total multiplicity of basis elements in `p` that are less than `a`
according to GHC's arbitrary ordering on types
introduced a couple of paragraphs ago.
The `FragLT` family only occurs in the contexts of `ext` and `prj` under `KnownFragCard`.
What is that class?

```haskell
*Main> :info KnownFragCard
class KnownFragCard (fr :: Frag k) where
  ...
*Main> :info Data.Frag.fragCard
Data.Frag.fragCard ::
  forall k (fr :: Frag k) (proxy :: Frag k -> *).
  KnownFragCard fr =>
  proxy fr -> Int
```

`Card` here abbreviates *cardinality*,
which is the total multiplicity of a multiset,
the sum of its multiplicities for each of the basis elements.
With the `fragCard` class method,
this class is just like `GHC.TypeLits.KnownNat :: Nat -> Constraint`,
but for our type-level integers instead of GHC's type-level naturals.
So `KnownFragCard (FragLT a p)` in the context mean `ext` and `prj` can get the run-time integer for the `FragLT` count.
That makes sense: `ext` needs to know where to put the new factor in the sorted linked list underlying a `Prod`,
and `prj` needs to know where to find it.
This integer is the *run-time evidence*/*dictionary* of the `p Lacks a` constraint from traditional row polymorphism.

Once you've used frags for a while, it will occur to you that the logic above seems to have a gap in it.
`FragLT a p` is the total multiplicity of basis elements that are less than `a`.
We saw above, for example, that `FragLT HumanID BestFriendTable` was `'Nil :+ '()`, ie 1,
since apparently `DogID < HumanID`.
But frags are *signed* multisets in which the multiplicities can be negative.
So what is, say, `FragLT c ('Nil :+ a :- b)`, assuming `a < c` and `b < c`?
It's 0, which seems problematic.
Actually, what does a product even mean with a negative factor?
What is `Prod ('Nil :- a) Identity`?

I only have the foggiest ideas what that could mean.
So the `motley` data structures cannot be used in that case.
But don't worry, the interface statically enforces that!
It just happens to be implicit in the types of `ext` and `prj`.
`Prod` is a Generalized Algebraic Data Type,
which means information about its run-time value has implications about its type indices.
In particular, the way `Prod` is defined ensures that its index frag is a proper set.
Therefore `FragLT a p` in the context of `ext` and `prj`
can safely assume that every multiplicity in `p` is positive (in fact, 0 or 1),
since they are both strict in their `Prod` argument.
*/me wipes brow*.

Wouldn't it be simpler to make frags just be sets?
Why have multisets, and especially why signed multisets?
Two answers, at least.
First, the choice of signed multiset is part of the particular point in the Haskell-row-polymorphism design space that this plugin is being used to explore.
In jargon, a signed multiset inhabits an __fr__ee __a__belian __g__ group (*frag*) has some nice properties
like *inverses* and *differences* for use in the constraint solver.
Second, beyond the typical expectations of products and sums, multiplicities beyond 1 or less than 0 could be very useful.
We've already seen that they can represent type-level integers (albeit using unary numerals…).

Maybe a plugin could get by with just sets.
But when I first was trying that during this work, it seemed significantly more complicated to implement,
at least in the context of GHC's constraint solving algorithm
and using the idea of "type families as syntax".
In my experience, using signed multisets both simplifies the plugin's implementation and increases the interface's expressivity.
The main cost is a more intricate interface and
-- except for `Prod`ucts --
somewhat pervasive `SetFrag fr` constraints.

Speaking of things that aren't `Prod`,
the `motley` package also defines `Sum`.
Whereas a `Prod p f` has a factor for each basis element in the set `p`,
a `Sum p f` is a summand for one of the basis elements in the set `p`.
For example, `Sum BestFriendTable Identity` is isomorphic to `Either HumanId DogId`.

```haskell
*Main> :info inj
inj ::
  forall k (a :: k) (p :: Frag k) (f :: k -> *).
  (FragEQ a p ~ 'Nil, KnownFragCard (FragLT a p)) =>
  f a -> Sum (p :+ a) f
*Main> :info alt
alt ::
  forall k (p :: Frag k) (a :: k) (f :: k -> *) ans.
  (SetFrag p ~ '(), FragEQ a p ~ 'Nil, KnownFragCard (FragLT a p)) =>
  (Sum p f -> ans) -> (f a -> ans) -> Sum (p :+ a) f -> ans
```

The `alt` combinator has that `SetFrag p` constraint that I was mentioning before.
Unlike `Prod`, a value `Sum p f` does not itself evidence that `p` is a set.
Otherwise the contexts are just the same `p Lacks a` constraints
as were in the `Prod` combinators.

The dual of `nil` is `absurd`.

```haskell
*Main> :i absurd
absurd :: forall k (f :: k -> *) a. String -> Sum 'Nil f -> a
```

With `alt` and `absurd`, we can build case expressions that decompose an entire `Sum`,
piece by piece.
For example, this expression converts `Sum ('Nil :+ a :+ b :+ c) f` to nested `Either`s.
(This seems related to the many comments at <https://www.reddit.com/r/haskell/comments/8ggssy/the_mysterious_incomposability_of_decidable/>,
but I haven't dug in yet.)

```haskell
*Main> :type (Left . (absurd "invalid Sum value!" `alt` Left `alt` Right)) `alt` Right
(Left . (absurd "invalid Sum value!" `alt` Left `alt` Right)) `alt` Right
  :: (KnownFragCard (FragLT a1 (('Nil :+ a2) :+ a3)),
      KnownFragCard (FragLT a3 ('Nil :+ a2)),
      SetFrag (('Nil :+ a2) :+ a3) ~ '(),
      FragEQ a1 (('Nil :+ a2) :+ a3) ~ 'Nil, SetFrag ('Nil :+ a2) ~ '(),
      FragEQ a3 ('Nil :+ a2) ~ 'Nil) =>
     Sum ((('Nil :+ a2) :+ a3) :+ a1) f
     -> Either (Either (f a2) (f a3)) (f a1)
```

The inferred context is fully of noisy details that amount to `{a1,a2,a3}` is a set
-- so none of them equals one of the others --
and GHC can figure out their order at a call-site.

I've shown here how

  * `nil` and `ext` let you build products one factor at a time
  * `absurd` and `alt` let you eliminate sums one summand at a time
  * `prj` lets you project a factor from a product
  * `inj` lets you inject a summand into a sum

But there are many more.

  * `ret` let's you split a product into a factor and a smaller product
  * `plusSum` let's you add a summand to a sum
  * `zipWithProd` is like the `<*>` of `Applicative`
  * `polyProd` is like the pure of `Applicative`
  * and so on

All of these build on the semantics of `Frag`, `:+`, and `:-`
and exercise the duality between product and sum types.

See

  * the [`frag` API][sec:frag-api] and [`motley` API][sec:motley-api] sections
  * the Haddock in `Data.Frag` and `Data.Motley`
  * the skeletons of use-cases in the `motley/test/*` directory and the `examples-motley` package

for more.

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

The kind `Frag b` can be described in many ways.
The most broadly familiar is to say it denotes all finite signed multisets of `b`s.
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
(This was intentional at the start; see <https://github.com/nfrisby/frags/issues/25>.)
We call a right partial application `:+ e` or `:- e` a *signed tally*.

The typechecker plugin simplifies equivalences at kind `Frag b`.
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
The next sections introduces another stepping stone towards the more familiar data structures.

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
We will see some in [Places][sec:motley-places] below.

## Nominal view
[sec:frag-nominal-view]: #nominal-view

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

This function is tagged as non-deterministic because the plugin will pop out basis elements in an arbitrary order.
I anticipate adding a `FragPop_Det` that only pops a basis element once the plugin determines its multiplicity
and also that it has no lessers according to `ORDER_STABLE`
(see <https://github.com/nfrisby/frags/issues/10>).

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
I'm continually impressed that the relatively simple frag interface suffices for defining the following data types.

I chose the name "motley" because the data types are *structural*, *extensible*, *anonymous*, etc --
they are *patchwork* compositions of parts,
reminiscent of a quilt formed of stitched together fabric pieces.
Moreover, you can just as freely decompose the types, like ripping some of those stitches.

## Places
[sec:motley-places]: #places

Picking up where [Universes][sec:frag-universes] left off,
we define a data type for codes of a anonymous closed universes.

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
that the order of the factors in the linked list is canonical.

This implementation as a linked list is inefficient,
but clearly demonstrates the expressivity of the simple frag interface.
Other data structures for products can have usefully different layouts in memory.
For example, <https://github.com/nfrisby/frags/issues/9> will investigate "flat" memory representations,
such as the "short vector" used in one of my deprecated earlier iterations, <https://github.com/nfrisby/coxswain>.

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
using the intuitive generalizations from `* -> *` to `(* -> *) -> *`.

```haskell
zipWithProd ::   -- <*>
  (forall a. f a -> g a -> h a) -> Prod fr f -> Prod fr g -> Prod fr h
polyProd ::  -- pure
  Implic (Prod fr U1) => (forall a. f a) -> Prod fr f
```

They are both also functors, foldable, traversable, etc
using the same generalization from `* -> *` to `(* -> *) -> *`.

TODO discuss `Implic`, which is implemented at type `Prod` via `FragPop_NonDet`

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
These rules are not exactly algorithmic,
though I have included some of the algorithmic/modal details --
they're more algorithmic than the usual presentations.
Moreover, I'm almost certain I've not yet included all the rules the plugin implements,
but the crucial ones are here.

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

The rules for `SetFrag` constrain every multiplicity in the frag to the interval `0 ≤ m ≤ 1`.

```haskell
-------------------- [SetFrag-Nil]
SetFrag 'Nil   ⟶   ()

-------------------- [SetFrag-one]
SetFrag ('Nil :+ a)   ⟶   ()

SetFrag fr
-------------------- [SetFrag-FragNE]
SetFrag (FragNE a fr)   ⟶   ()

a is not manifestly '()
-------------------- [SetFrag-tally]
SetFrag (fr ? :+- a)   ⟶
  ( SetFrag (FragNE a fr) , SetFrag (FragEQ a fr :+- '()) )
```

```haskell
-------------------- [KnownFragCard-Nil]
KnownFragCard 'Nil   ⟶   0

-------------------- [KnownFragCard-tally]
KnownFragCard (fr :+- a)   ⟶   KnownFragCard fr +- 1
```

### Relations

```haskell
-------------------- [EqFrag-Nil-Nil]
EqFrag 'Nil 'Nil   ⟶   ()

-------------------- [EqFrag-tally]
EqFrag (frL :+- a) frR   ⟶   EqFrag frL (frR :-+ a)

r is not manifestly 'Nil
-------------------- [EqFrag-difference]
EqFrag r EXT(r,e)   ⟶   EqFrag 'Nil EXT('Nil,e)

r is not manifestly 'Nil
-------------------- [EqFrag-swap]
EqFrag 'Nil EXT(r,e)   ⟶   EqFrag r EXT('Nil,NEGATE(e))
```

See also the rules in [Improvement][sec:internals-rules-improvement] below.

**Discussion**
The following rules are sound and in some sense more complete than the above,
but not reflective of the implementation.

```haskell
r is not manifestly 'Nil
-------------------- [FOR-DISCUSSION-EqFrag-swap]
EqFrag r EXT('Nil,e)   ⟶   EqFrag 'Nil EXT(r,NEGATE(e))

a is not manifestly '()
-------------------- [FOR-DISCUSSION-EqFrag-Nil-tally]
EqFrag 'Nil (fr ? :+- a)   ⟶
  ( EqFrag 'Nil (FragNE a fr) , EqFrag 'Nil (FragEQ a fr :+- '()) )
```

The key differences are:

  * When at least one of the roots is a type variable,
  the plugin interprets the `EqFrag` constraint as a mapping in a substitution.
  For example, `EqFrag tv ('Nil :+ a :+ b)` is interpreted
  as a mapping from the type variable `tv` to the frag `'Nil :+ a :+ b`.
  (When both roots are type variables,
  various technical considerations motivate which to substitute for.)
  The `[FOR-DISCUSSION-EqFrag-Nil-tally]` rule would interfere with this.

  * Relatedly, whereas `[FOR-DISCUSSION-EqFrag-swap]` prefers to isolate `'Nil` on the left-hand side,
  `[EqFrag-swap]` prefers non-`'Nil`.

  * `[FOR-DISCUSSION-EqFrag-Nil-tally]` decomposes the frag the frag into several `EqFrag 'Nil (FragEq ...)` constraints,
  just as does `[SetFrag-tally]`.
  Such constraints enable improvements via `[EqFrag-Nil-FragEQ-Nil-improve-neg]` and `[EqFrag-Nil-FragEQ-Nil-improve-pos]` in the
  in [Improvement][sec:internals-rules-improvement] below.
  In the absence of `[FOR-DISCUSSION-EqFrag-Nil-tally]`, we must add the additional rules `[EqFrag-Nil-Nil-improve-pos]` and `[EqFrag-Nil-Nil-improve-neg]`,
  in order to recover the same improvements directly from `EqFrag` constraints with two `'Nil` roots.

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
[sec:internals-rules-improvement]: #improvement

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
-------------------- [EqFrag-Nil-FragEQ-Nil-improve-pos]
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
-------------------- [EqFrag-Nil-FragEQ-Nil-improve-neg]
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

### Inert Frag Substitution

TODO elaborate

We interpret a given equivalence between frags (ie `~` and `EqFrag`) that have a type variable root on at least one side as a substitution mapping.
For example, `(x :+ a) ~ (y :+ b)` will either map `x` to `y :+ b :- a` or map `y` to `x :+ :- b` --
which one depends on various and sundry technical details.

In this way, the plugin maintains and applies a substitution over frag type variables
in addition to the multiplicity and apartness tables.

## Normalization
[sec:internals-normalization]: #normalization

TODO be consistent throughout calling this either canonicalization or normalization; pick one.

The plugin uses `ORDER_FRAGILE` to ensure that the tallies in every extension
and every nested `FragNE` chain use a consistent order.
The goal of such *normalization* is for semantically equivalent types to be syntactically equal types.
This is quite inefficient, but given the current GHC plugin interface, it is in some ways the only option.
In particular, there are parts of GHC that check for equality/unification of two types
that we would like to be aware of commutativity,
but that plugins are unable to directly affect.

TODO what the plugin could do without normalization (eg simplify equivalences)

TODO what the plugin can only do with normalization (eg avoid diverging from repeated fundeps)

TODO what the plugin cannot do even with normalization (eg simplify inferred types)

TODO how we normalize: via the inert frag substitution and the frag unflattening substitution

## Floating equivalences
[sec:internals-floating-eqs]: #floating-eqs

Given `SetFrag` and/or `Apart` constraints must prevent GHC from floating Wanted `~` constraints out of their implication scope;
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

## Congruence Closure
[sec:internals-congruence-closure]: #congruence-closure

TODO explain how the plugin manages its own inert set

### Splitting Derives

TODO explain <https://github.com/nfrisby/frags/issues/31>
