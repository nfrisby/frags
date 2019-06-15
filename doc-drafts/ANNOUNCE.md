---
title: ANNOUNCE: frag-0.1 and motley-0.1
author: Nicolas Frisby
date: 2019 June
---

# Announcement

  * The `frag` library defines a typechecker plugin that provides a limited form of row polymorphism.
  * The `motley` library uses that plugin to define extensible structural data types.

<http://hackage.haskell.org/package/frag> - <http://hackage.haskell.org/package/motley>

### Should we use it right now?

These libraries are currently *not even alpha* quality.
Use at your own risk.
I'm releasing to pique interest, and because I want collaborators! :)

The license is currently BSD3.
(I'm flexible on this, if companies need something else.
Please reach out.)

### How to use it?

However you're accessing this file should also provide a `docs/README.md` file;
it has lots of content, notably including a `#how-to-use` section and a `#tutorial` section.
The Haddock in the user-facing modules includes plain-speak descriptions
except where the types themselves should already be very clear.

### What is it supposed to do?

Concretely, it's a GHC typechecker plugin that implements row polymorphism
and a set of generic libraries that are directly enabled by such a thing: records, variants, etc.
This is just the first iteration.
In particular, it doesn't provide full row polymorphism,
but it does do something very similar.

The ultimate goal is to design a `LANGUAGE` extension for row polymorphism in GHC itself.
This plugin is a vehicle to get some practical experience
exploring this point of the rich design space for Haskell row polymorphism.
And it might even become mature enough itself to be useful to people in the near-term --
extending GHC's type-checker will probably take a relatively long time.

### Really though, what does it do *today*?

The `frag` library defines a typechecker plugin that provides a limited form of row polymorphism.
The limitation is that each label in the row must be its own payload:
`{"foo": "foo", "bar": "bar"}`, `{Int: Int, Bool: Bool, x:x}`, etc.
Therefore, these are more so type-level sets than row types.
At least for now, though, `frag` is focused on the traditional row type interface,
excluding binary operations like union/intersection/etc,
for the sake of simplicity.
Since they are somewhat peculiar and also more general than sets --
and "type-level set" is a mouthful anyway --
I call them *frags* and say that the plugin provides *frag polymorphism*.

Rows and row polymorphism are still the long-term goal,
but frags have a pleasantly surprising power-to-weight ratio.

The `motley` library uses the `frag` library to define structural data types indexed by frags.
Primarily, `motley` defines the frag-indexed sum and product types `Sum p f` and `Prod p f`,
where `p :: Frag k` is a set frag and `f :: k -> *`.
Recognize these as less general forms of row-indexed polymorphic variants and records.

Here's a taste.

```haskell
$ cabal v2-repl motley:test:test-Motley
*Main> :set -XFlexibleContexts -XTypeFamilies
*Main> :set -fplugin=Data.Frag.Plugin -dcore-lint
*Main> :set -fconstraint-solver-iterations=10
*Main> let x = nil `ext` Identity (3 :: Int) `ext` Identity True `ext` Identity 'z'
*Main> let y = nil `ext` Identity True `ext` Identity 'z' `ext` Identity (3 :: Int)
*Main> :type x
x :: Prod ((('Nil :+ Int) :+ Bool) :+ Char) Identity
*Main> :type y
y :: Prod ((('Nil :+ Bool) :+ Char) :+ Int) Identity
*Main> mapM_ print [x,y]
{(Identity True) (Identity 3) (Identity 'z')}
{(Identity True) (Identity 3) (Identity 'z')}
```

And a simple use of frag polymorphism.

```haskell
*Main> let prjI p = runIdentity (prj p)
*Main> let f p = prjI p + maybe 0 id (prjI p) :: Int
*Main> f (nil `ext` Identity 3 `ext` Identity Nothing)
3
*Main> f (nil `ext` Identity 3 `ext` Identity Nothing `ext` Identity 'c')
3
*Main> f (nil `ext` Identity 3 `ext` Identity 'c' `ext` Identity Nothing)
3
*Main> f (nil `ext` Identity 3 `ext` Identity 'c' `ext` Identity (Just 4))
7
```

The plugin's power is most apparent when the frags involve type variables.
There be dragons in these types,
but I'm continually working to make the individual ingredients as straight-forward as I can.
Some of it has to do with limitations of the GHC plugin interface,
I have been and will continue opening Issues on GHC's GitLab;
likely to work on them too.

```haskell
*Main> let z = nil `ext` Identity 3 `ext` Identity True `ext` Identity 'z'
*Main> :type z
z :: (KnownFragCard (FragLT Char ('Nil :+ a)),
      KnownFragCard (FragLT Bool ('Nil :+ a)), Num a,
      Data.Frag.Apart ('Data.Frag.OneApart a Bool) ~ '(),     -- ie a /~ Bool
      Data.Frag.Apart ('Data.Frag.OneApart a Char) ~ '()) =>     -- ie a /~ Char
     Prod ((('Nil :+ a) :+ Bool) :+ Char) Identity
*Main> :type f
f :: (KnownFragCard (FragLT Int p),
      KnownFragCard (FragLT (Maybe Int) p),
      Data.Frag.EqFrag (FragEQ Int p) ('Nil :+ '()) ~ '(),     -- ie Int is in p once
      FragEQ (Maybe Int) p ~ 'Nil) =>     -- ie Maybe Int is in p zero times
     Prod (((p :- Int) :+ Maybe Int) :+ Int) Identity -> Int
*Main> f nil

<interactive>:6:1: error:
    • Couldn't match expected type ‘'()’     -- ie Int is not in 'Nil :- Maybe Int once
                  with actual type ‘Data.Frag.EqFrag
                                      (FragEQ Int ('Nil :- Maybe Int)) ('Nil :+ '())’
    • In the expression: f nil
      In an equation for ‘it’: it = f nil
```

See the `#how-to-use` and `#tutorial` sections of the adjacent `docs/README.md` file for how to get started.

### How does it do that?

The `frag` library declares several simple types, type families, and classes,
but it doesn't declare many instances of the families.
These *mostly uninterpreted* type families serve as syntax for frags.
Then the plugin extends the GHC constraint solver
to also handle the frag interface's families and classes correctly.

In particular, the plugin ensures GHC considers two frags with the same basis elements in different orders as `~`-equivalent types.

### What does it not do yet?

Here is a list of the known limitations that come to mind.
I think they can all be overcome with more work.

  * Nesting frags withing frags just might work if you're lucky.
  * Frags in kinds will not work unless you're very lucky (ie if they would already work without the plugin).
  * <https://gitlab.haskell.org/ghc/ghc/issues/16639> prevents the plugin from letting GHC's pattern checker recognize unreachable cases.
  * The error messages are unclear.
  * The inferred types are messy.
  * There are very likely several bugs. (**Do not forget** to pass `-dcore-lint` to GHC.)
  * The plugin doesn't implement much frag theory beyond what `motley` and my few test cases have required.
  * I have not tuned the code to generate efficient GHC Core.

### How can we improve it?

If you're willing to spend your time on this project, any Issues and Pull Requests at all will be appreciated!
I'm confident a core team will manifest around this as people determine how much energy they want to invest.

At the moment, I think the project would benefit most from a community-sourced test suite.
I'm excited for brave alpha-testers to find shiny use-cases for `frag` and `motley` --
in their non-essential work! --
and thereby flush out bugs, highlight weak documentation, and prioritize new features.
(And my personal experience is that writing use-cases has been pretty fun!)
The upside is that the libraries' user-interface is much simpler than the implmentation,
so "being a alpha user" is a comparatively easier way to collaborate.

Frankly, the plugin itself is complicated,
mired in many of the details of the GHC internals.
The project documentation is all first-draft.
The source code is obviously the result of research and exploration:
it's under-commented and the architecture has accumulated organically in fits and starts.
The tests are thin.
This has been my hobby project and learning vehicle.
It's everyone's nightmare codebase.
So again: **don't use this version for important things!**

I really want to pay that debt down.
I think it's the greatest obstacle to growing a team around this stuff.
It feels like my burden to bear -- my mess to clean-up --
but if you're incredibly motivated, please have at it.
I'll answer as many of your questions as well as I can.
I do have a road map to make it easier (within a few months?) for others to work on the source.

  1. Respectable community-sourced test suite.
  1. Refactor -- find (more) minimal rule sets, etc.
  1. Thorough comments and architectural overviews of the well-organized code.
  1. Actively invite people to wade into the source itself.

I know that route is idealistic, but I'm going to give it a chance.
The basic idea is to prioritize more tests and a non-zero amount of community input
regarding priorities before refactoring code and writing deeply detailed documentation.

Thank you for your consideration!
