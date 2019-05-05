% `frag`: A Typechecker Plugin for Ornamented Signed Tallies
% Nicolas Frisby
% 2019 May 5

# Introduction

The `frag` Haskell package implements a typechecker plugin and library
for a theory of *ornamented signed tallies*,
which is a spartan signature for multisets with multiplicities from ℤ.
This is a useful step on the path towards row types and row polymorphism in GHC.

# Introduction Forms

The signature has the following introduction forms.

```{.haskell}
Frag :: k -> Type
'Nil :: Frag k
(p :: Frag k) :+ (a :: k) :: Frag k
(p :: Frag k) :- (a :: k) :: Frag k
```

`Frag ()` is inhabited by types that denote integers:
`'Nil` is zero,
`x :+ '()` is the successor of `x`,
and `x :- '()` is the predecessor of `x`.
We therefore refer to partial applications of `:+` and `:-` as *(signed) tallies*.

When `k` is more varied than `()`,
each inhabitant of `Frag k` is an *ornamented* integer,
in which those tallies with the same (equivalent) ornament together denote that ornament's multiplicity.
`Frag k` is thereby inhabited by types that denote multisets over the basis `k`;
`'Nil` is the empty multiset, and each tally increments or decrements its ornament's multiplicity.

# Equivalence

In particular, the theory disregards the syntactic order of tallies
when judging equivalence at kind `Frag k`.
This is implemented via a tally-based analog of free abelian group unification.
For example, we have `(x :+ a :+ b) ~ (x :+ b :+ a)`, `x ~ x :+ a :- a`, and so on.
Moreover, the plugin is carefully integrated with GHC's constraint solver
such that type inference performs well.
For example, the plugin simplifies the constraint
`('Nil :+ a :+ Int) ~ ('Nil :+ Int :+ Char)` to `a ~ Int`.

# Beyond Equivance

The signature and theory also include
the following eliminators, predicates, and evidence.

```{.haskell}
FragCard :: Frag k -> Frag ()   -- total multiplicity
FragEQ :: k -> Frag k -> Frag ()  -- multiplicity
FragLT :: k -> Frag k -> Frag ()  -- total multiplicity of all elements < a
FragNE :: k -> Frag k -> Frag k   -- set multiplicity of a to 0

SetFrag :: Frag k -> Constraint   -- each multiplicity is 0 or 1

KnownFragCard :: Frag () -> Constraint
fragCard :: forall p proxy. KnownFragCard p => proxy p -> Int
  -- NB the plugin crashes before this `Int` overflows
```

All together, the package enables users to define frag-indexed types
(thereby extensible, anonymous, and structural)
and frag polymorphic values (*c.f.* *row polymorphism*).
Such data types include
finite type universes,
type-indexed sums,
and type-indexed products.

# Future Work

The frag introduction forms notably omit all binary operators,
especially the free abelian group operator of multiset addition/union.
("Frag" is derived from *fr*ee *a*belian *g*roup
but also *frag*ment to emphasize this omission.)
These operators will significantly increase the complexity of
the theory and the plugin's implementation.

Rows generalize frags.
Specifically, a frag is a row type in which each component is its own label.

The plugin pushes the envelope of the GHC plugin interface.
This package would benefit from improvements to that interface.
And ultimately, the best user experience would come from integrating the frag theory into GHC itself.

Though much interesting work remains,
even just frags and tallies seem useful.
