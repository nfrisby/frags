# GHC internals
[sec:ghc-internals]: #ghc-internals

Because the frag plugin simplifies `~` constraints among others,
it must be carefully designed to cooperate with GHC's equality constraint solver.
While the basic GHC plugin interface itself is relatively simple,
the GHC constraint solver is not.
This section summarizes both,
focusing on the concerns of the plugin.
I'm limiting my discussion to the behavior of GHC 8.6.4.

I've also written up some terser notes that do not mention frags at all.

  * https://gitlab.haskell.org/ghc/ghc/wikis/plugins/type-checker/notes

## Plugin interface
[sec:ghc-internals-plugin-interface]: #plugin-interface

As part of its constraint solving loop,
GHC allows active typechecker plugins to alter the set of constraints.
That is currently the only way a plugin can affect typechecking.
Because GHC runs its constraint solver in many ways,
not only for checking user code for type errors,
the plugin's contribution to constraint solving
can have a significant affect on the user experience.
(And the plugin author may have a difficult time
determining exactly which parts of a program
caused a particular invocation of the plugin!)

GHC invokes the `TcPluginSolver` function provided by a plugin.

```haskell
type TcPluginSolver =
  [Ct] -> [Ct] -> [Ct] -> TcPluginM TcPluginResult

data TcPluginResult
  = TcPluginContradiction [Ct]
  | TcPluginOk [(EvTerm,Ct)] [Ct]
```

The plugin receives three sets of constraints: Givens, Deriveds, and Wanteds.
The plugin can either identify
a (TODO non-empty?) set of constraints as self-inconsistent
or solve some constraints and/or introduce some new ones.
To simplify/split/decompose a constraint,
introduce simpler new ones and use them to solve the old one.
If the plugin has nothing to contribute,
it should solve none and introduce none: `TcPluginOk [] []`.
If the plugin creates any new constraints,
GHC will simplify them and then call the plugin again.

### Wanteds

Wanteds are simply the constraints that GHC is trying to solve.
Any occurrence of an identifier with a qualified type
-- such as `(==) :: Eq a -> a -> a -> Bool`,
`foo :: Bar a => a`,
and `Refl :: (a ~ b) => a :~: b` --
will induce a Wanted from the context of that qualified type.
Moreover, function application inherently requires
that the domain and the argument's type match.
GHC only tries so hard to unify two types when checking user source
and defers the more interesting cases by creating a corresponding `~` constraint.

Notably, equivalences involving our frag tallies end up as `~` constraints,
which our plugin eventually has the opportunity to help GHC simplify.
If frag tallies were type constructors instead of type family applications,
their equivalences would not be interesting enough to induce `~` constraints:
GHC would treat them like any other type constructor
and frag equivalences involving commutativity
would simply cause immediate unification failures.

### Evidence

To solve a Wanted constraint, the plugin must provide evidence for it.
Evidence is ultimately an expression in the same internal representation
that GHC uses for user expressions: GHC Core.
The plugin must therefore use the GHC API to construct Core terms as evidence.
(GHC trusts these terms respect its internals invariants.
It is not an easy task,
so I recommend enabling `-dcore-lint` in any module that uses a plugin.)
The type of an evidence term is quite literally the constraint's predicate itself:
each type class determines a data type with one type parameter per class index
and one constructor with an argument for each class method,
and `~` constraints are inhabitated by *coercions* (a subset of Core).

Of the many ways to create an evidence term, two are essential to a plugin.

  * The plugin can reuse an existing evidence term at a different type.
    This involves creating a corresponding coercion,
    usually by fiat: see the `UnivCo` constructor for the `Coercion` type.
    This coercion represents the domain-specific type rule
    that the plugin knows how to apply and GHC alone does not.

  * The plugin can refer to the evidence of constraints,
    since each `Ct` includes the identifier for its evidence variable.

### Deriveds

The need for evidence is rooted in the theoretical underpinnings of Haskell --
see <http://homepages.inf.ed.ac.uk/wadler/topics/type-classes.html#class> and <http://homepages.inf.ed.ac.uk/wadler/topics/history.html#propositions-as-types>.
Even so, some programs do not actually use the evidence of all their Wanted constraints.
Deriveds are the special case of Wanteds without evidence.

The entire purpose of Deriveds is to drive additional unifications beyond the Wanteds.
Roughly, GHC treat Deriveds a bit more liberally than Wanteds,
and so can find additional type equalities.

See my notes on the GHC wiki for more details about Deriveds.

  * https://gitlab.haskell.org/ghc/ghc/wikis/plugins/type-checker/notes

The plugin currently has only partial support for Deriveds --
https://github.com/nfrisby/frags/issues/31 tracks full support.
My basic plan is to refine it as I find test cases for it.

### Givens

Givens are the constraints that GHC has available as assumptions;
their primary purpose is to provide evidence variables
for building up evidence for Wanteds.
Givens arise from the contexts in user-provided signatures
like `sort :: Ord a => [a] -> [a]`
and the contexts of a GADT constructor occurring in a pattern
like `(a ~ b) => Refl :: a :~: b`.

GHC sometimes invokes the plugin with only Givens and no Deriveds or Wanteds.
This gives the plugin a somewhat optional opportunity to simplify the Givens.
If the plugin reports a contradiction in the Givens,
then GHC will know that the case alternative
in which those Givens are in scope
is unreachable
(though see <https://github.com/adamgundry/uom-plugin/issues/22#issuecomment-244724840> and <https://gitlab.haskell.org/ghc/ghc/issues/16639>).
If some Givens are/become redundant,
then the plugin can tell GHC to discard them
by returning a `TcPluginOk` that "solves" them --
the provided evidence is ignored,
and the convention therefore seems to be to supply the constraint's own evidence.
To create new Givens,
one must provide an evidence term built up from the existing Givens.

### Given-Wanted duality

The GHC API for plugins to create new constraints includes the following.

```haskell
newWanted  :: CtLoc -> PredType -> TcPluginM CtEvidence
newGiven :: CtLoc -> PredType -> EvExpr -> TcPluginM CtEvidence

mkNonCanonical :: CtEvidence -> Ct   -- and others
```

The `EvExpr` in `newGiven` is essentially the same
as the `EvTerm` in `TcPluginOk`,
highlighting a fundamental duality:
you must provide evidence to *solve* a Wanted
while you must provide evidence to *create* a Given.
This duality is more intuitive when you realize that
the GHC Core for a user expression involving coercions and/or class methods
includes corresponding occurrences of the Wanteds' evidence variables.
Roughly speaking,
those variables (Wanted) are bound by `let`s, in which the RHS
includes occurrences of other evidence variables (Wanteds and/or Givens),
in turn bound either by similar `let`s (and so on) or by
implicit formal arguments of the user expression (Givens).

## Constraint solver
[sec:ghc-internals-solver]: #constraint-solver

The plugin must cooperate with GHC's own constraint solver.
The best reference I'm aware of is <https://www.microsoft.com/en-us/research/publication/outsideinx-modular-type-inference-with-local-assumptions/>.
Its design is non-trivial and plugin authors
-- especially those tinkering with `~` constraints --
need to understand it for at least two reasons:
many of its implementation details "leak" into the plugin interface,
and (relatedly) it is extremely easy for plugins to instigate an endless loop
by making some change that the GHC constraint solver will immediately undo.
(The compiler's default iteration limits raise an error quickly in this case;
it's rarely a false positive).

This section summarizes my understanding of GHC's constraint solver.
It's skewed toward `~` constraints because the frag plugin focuses on those,
but they do seem to be the crux of the solver.

### Inert set

The solver maintains a set of constraints call the *inert set*.
Each element is called an *inert constraint* or just *an inert*.
The key invariant is that no inert can affect another:
imply, contradict, or simplify it or similar.
The *OutsideIn(X)* authors explain exactly what *affect* means,
though some details are now likely some out-of-date or missing.
The inert set is where the solver accumulates its progress.
It's comparable to a unification algorithm's *most general unifier*:
it's the partial solution so far
and must be as general as possible.
As the *OutsideIn(X)* authors phrased it, the inerts are "free of guesses".

The solver loop also maintains a worklist of non-inert constraints.
The loop body checks if any inert affects the next worklist item.
If the item passes the gauntlet of all the inerts,
then the solver makes those checks in reverse,
*kicking out* any previously inert constraint
that the new one affects,
thus maintaining the inert set invariant.

I have a few more assumptions about the loop.

  * If an inert affects a work item or vice versa,
    then the affectee is immediately suitably refined
    such that the affector no longer affects it.

    In particular, any constraint being placed **back** on worklist
    must have been so refined in order to ensure the loop can terminate!

  * It's optimized to not actually use two passes,
    but I think of it as two passes.

  * There is a generic name for this basic algorithm,
    but I'm not recognizing it beyond the parallels with unification.
    (Perhaps it is "congruence closure"?)
    This is one of many other aspects of this project that
    encourages me to better familiarize myself
    with the constraint solving and term rewriting literature.

### Canonicalization

I'm skipping over the details of GHC's *canonicalization* step,
since I think of it as the empty inert set affecting a constraint.
For example,
`Int ~ Int` is implied,
`Int ~ Char` is contradicted,
`(a,b) ~ (x,y)` is simplified to `(a ~ x,b ~ y)`,
etc.

Some details of canonicalization are relevant,
however, if only because they influence the `Ct` data type.
Its constructors encode structure
that is determined during canonicalization.
There is one `*Can` constructor for each useful variety of canonical constraint
and also the catch-all `CNonCanonical` constructor.
(TODO Does `CNonCanonical` only mean "not yet canonicalized"
or sometimes "could not be canonicalized"?)
I only discuss some of these `*Can` constructors in this document,
the ones I've had to learn about.

### Flattening

A `CFunEqCan` is a `~` constraint
with a type family application on the LHS and a *flattening* tyvar on the RHS.
The constraint is the definition of the flattening tyvar,
though not the binder.
GHC introduces these `CFunEqCan` constraints
by *flattening* constraints during canonicalization.

Flattening is a term rewriting technique,
used to simplify how GHC handles constraints involving type family applications.
In particular, if an application of a (non-injective) type family
does not match any of that family's instances,
then that application is -- at least temporarily -- *uninterpreted*,
equal only to itself.
For that reason, GHC flattens all type family applications to *fresh* tyvars,
working very hard to replace all applications
of the same family to the same arguments with the same tyvar.
Then the rest of the constraint solving machinery,
though unaware of type family semantics,
will still treat them correctly just by treating variables correctly.

GHC creates fresh fsks and new `CFunEqCan` Givens when flattening a Given
and creates fresh fmvs and new `CFunEqCan` Wanteds when flattening a Derived or Wanted.
However, GHC currently unflattens Wanteds (not Givens) before invoking the plugin,
so plugins don't see fmvs or Wanted `CFunEqCan`s.
I opened <https://gitlab.haskell.org/ghc/ghc/issues/15147>, because
I misunderstood what was meant by "unflattening Wanteds".
It means that the `CFunEqCan`  Wanteds are eliminated
by substituting their LHS for every occurrence of their fmv.
What had confused me is that fsks can still occur in unflattened Wanteds,
since the `CFunEqCan` Givens are still in effect.
The comments on that ticket suggest that plugins
will eventually received the flattened Wanteds.
(I have seen univars in Givens, so I suspect fmvs can occur in Givens as well.)

We discuss `CTyEqCan` constraints in the next section,
but it's appropriate to explain here that sometimes,
after various interactions,
a `CTyEqCan` serves double duty as a `CFunEqCan`
by defining one flattening tyvar to be an *alias* for another type.
If you follow a chain of aliases that link flattening tyvars,
you'll eventually reach a `CFunEqCan`.
Valid `CFunEqCan`s and `CTyEqCan` aliases can depend on each other,
but never form a cycle
-- that would correspond to a syntactically infinite type family application.

### Inert substitution

A `CTyEqCan` is a `~` constraint with a tyvar on the LHS
that does not occur on the RHS (TODO occurs check exceptions?).
Such a constraint will affect any other in which that tyvar occurs,
refining the affectee by substituting the RHS for the variable.
Also, if the constraint is a Wanted,
the tyvar is a unification variable,
and various other conditions are satisfied,
then GHC will solve the constraint
by assigning the RHS to the unification variable.

A `CTyEqCan` with a tyvar on both sides
requires an interesting design decision.
Should it be `tv1 ~ tv2` or `tv2 ~ tv1`?
Unfortunately, the simple answer "leave it how you found it" is insufficient.
GHC has changed it answer to this question more than once;
there are subtleties.

GHC compares the *level* of the tyvars,
and breaks ties by comparing the *flavor* of the tyvars.
If the flavor is also the same,
GHC does some more checks only for the sake of improving the user experience,
like preventing ephemeral tyvars from showing up in error messages.
Otherwise, it leaves the orientation as it found it.

I don't understand `RuntimeUnk` or `SigTv`,
so I think in terms of only four flavors:
skolem tyvars (`tv`),
flattening skolem tyvars (`fsk`),
meta-/mutable-/unification-vars (`tau`),
and flattening metvars (`fmv`).
That list is in order of increasing priority for the LHS,
so that GHC most prefers fmvs on the LHS and least prefers skolems on the LHS.
Because of the consequences of `CTyEqCan` orientation,
this means that the GHC prefers
to assign (especially flattening) univars or else eliminate their occurrences
more than it prefers to eliminate occurrences of (especially flattening) skolems.

Regardless of flavor,
GHC prefers a tyvar with a deeper level on the LHS.
The level of a tyvar is the number of `forall`s
that enclose the `forall` that binds it.
Levels can be subtle in surface Haskell syntax,
since so many `forall`s are often implicit.
The trickiest is probably that a qualified type `=>`
always introduces a `forall`, possibly binding zero tyvars.
And there are also many ways that `forall`s can enclose others:
higher-rank types,
nested `let` bindings,
nested `where` clauses,
patterns with constructors
that have `forall`s in their signature (existential and/or GADT),
and class methods, which inherit one `forall` from their class
and might have another from their signature.
I'm probably missing some ways too.

For a simple example, in the following declaration,
`hof` has level 1,
`f` and `g` have level 2,
and `a` has level 3.
(TODO 0 is reserved for fmvs, right?)

```haskell
class HoFunctor hof where
  hofmap :: (forall a. f a -> g a) -> hof f -> hof g
```

All of the `CTyEqCan`s together effect a substitution
called the *inert substitution*.

### Floating equivalences

As explained in *OutsideIn(X)*,
GHC keeps track of which level it's currently operating on,
and it will never assign any type to a univar
whose level is shallower than the current level
Since there should be no univars with a level deeper than the current level,
that means GHC will only assign univars of the current level.

That simple rule prevents `~` constraints brought into scope by a GADT pattern
from influencing univars bound outside of that pattern,
ensuring that such local `~` constraints
only affect univars bound in their scope.
However, not every `forall` involves `~` constraints,
so GHC *floats* promising `~` Wanteds out from under `forall`s
that do not have any `~` constraints
and don't bind any variables in the Wanted being floated.
Ideally, the LHS of a `~` Wanted is a univar,
the constraint floats all the way up to the univar's level,
and GHC then solves the constraint by assigning the RHS to the univar.
Note that the inert substitution
-- which prefers to eliminate tyvars with deeper levels --
might eliminate variable occurrences in a Wanted that
had been preventing it from floating past their binding `forall`.

The ultimate requirement is that a Wanted must not float past a Given that
provides evidence that might be necessary to solve the Wanted.
Since GHC only floats `~` Wanteds, everything roughly simplifies to:
`~` Givens, and any Given that might become/imply a `~` Given, prevent floating.
There are some exceptions <https://gitlab.haskell.org/ghc/ghc/issues/15009>
(and I think there should be more <https://gitlab.haskell.org/ghc/ghc/wikis/float-more-eqs2018>
but haven't yet worked through the details).

Plugin authors should ensure that any constraint
that the plugin might simplify to a `~` is already recognized by GHC
as a constraint that should block floating.
Otherwise GHC might float constraints out from under it
before the plugin is able to reveal it as a blocker.
(As far as I know, that currently means the constraint must either be a `~`,
be a type family application,
or be able to reach one of those via superclasses.)
