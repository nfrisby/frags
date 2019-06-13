---
title: ANNOUNCE: frag-0.1 and motley-0.1
author: Nicolas Frisby
date: 2019 June
---

# Announcement

  * The `frag` library defines a typechecker plugin that provides a limited form of row polymorphism.
  * The `motley` library uses the `frag` library to define structural data types indexed by frags.

<http://hackage.haskell.org/package/frag> - <http://hackage.haskell.org/package/motley>

# Disclaimer

These libraries are the result of a few years of hobby programming in my free time.
The motivation has been and still is just as much to learn about GHC's implementation as it is to provide (something like) row polymorphism.
I would be delighted for others to contribute and refine this work into reliable resource for the community.
And I would be unbearably happy if a more consistently active GHC dev than myself finds it inspiring
enough to go ahead and distill a proper GHC language extension from it!
I'd be quite eager to provide what guidance I can and to co-author a publication.

These libraries are currently *not even alpha* quality.
I'm releasing to pique interest, and because I want help! :)

# Overview

The aforementioned limitation of `frag` is that each row label is its own payload:
`{"foo": "foo", "bar": "bar"}`, `{Int: Int, Bool: Bool, x:x}`, etc.
Therefore, these are type-level sets more so than row types.
At least for now, though, `frag` is focused on the traditional row type interface,
excluding binary operations like union/intersection/etc,
for the sake of simplicity.
Since they are somewhat peculiar and also more general than sets --
and "type-level set" is a mouthful anyway --
I call them *frags* and say that the plugin provides *frag polymorphism*.

Rows and row polymorphism are on the longer-term schedule,
but frags have a pleasantly surprising power-to-weight ratio.

Primarily, `motley` defines the frag-indexed sum and product types `Sum p f` and `Prod p f`,
where `p :: Frag k` is a set frag and `f :: k -> *`.
Recognize these as less general forms of row-type indexed polymorphic variants and records.

# Demonstration

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

The plugin's power is ultimately apparent when the frags involve type variables.
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

Remarkable known current limitations (these can be overcome with more work):

  * Nested frags might work if you're lucky.
  * Frags in kinds will not work unless you're very lucky.
  * <https://gitlab.haskell.org/ghc/ghc/issues/16639> prevents the plugin from letting GHC's pattern checker recognize unreachable cases.
  * Unclear error messages.
  * Unclear inferred types.
  * Very high likelihood of bugs.
  * Plugin doesn't implement much frag theory beyond what `motley` and my few test cases have required.

# How to Help

The current source is pretty obviously the result of research and exploration;
it's under-commented and has accumulated rather organically.
It's so far a hobby project.

I'll be paying that debt down, especially if there's a big positive community response.
But I'd like more and better tests in place
before prioritizing refactoring and thorough code-level documentation.

Thus, my request for help at this stage is for brave alpha-testers to try using `frag` and `motley` --
in their non-essential work! --
and to contribute case studies, bug reports, and test cases.
Road map:

  1. Respectable community-sourced test suite.
  1. Refactor -- find minimal rule sets, etc.
  1. Thorough comments of the well-organized code.
  1. Invite others to contribute to a well-organized source base of the plugin itself.
  1. ... lots of cooperative work ...
  1. Extend GHC itself and publish a paper.

I know that route is idealistic, but I'm going to give it a chance.

Thank you for your consideration!
