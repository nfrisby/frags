# Context for this work

I've developed this typechecker plugin as a hobby passion project over the last few years.
The aim has always been twofold:
to learn about GHC's type checker
and to make a proof-of-concept compelling enough that
an active GHC developer/researcher could not resist the urge
to distill a proper GHC patch out of it for /row polymorphism/.
I've learned a lot, and there's thankfully no end in sight on that front.
And of the several from-scratch iterations I've done in private,
I'm delighted to finally share one that feels promising!

This repo was, is, and will remain a hobby project.
My work on it will continue to be bursty.
I'm excited to cooperate with you!
But my bandwidth will remain limited.

Thanks. -Nick

# Code

It's not quite yet row types,
but it's already very compelling.
And very **experimental**;
I have no doubt there are bugs and that you'll find them.
Some exciting examples do already work, though,
which is why I'm sharing now.

The `frag` package defines the types and the typechecker plugin.
The `motley` package uses them
to implement `n`-ary product and sum data types.
Like the *row type*-indexed records and polymorphic variants,
the *frag type*-indexed products and sums are anonymous/structural, extensible, and unordered.
Unlike row types, the components are type-indexed instead of labeled.
There is a good example in the [motley.cabal](motley/motley.cabal) description.

The type errors will unfortunately test your mettle.

I'm still charting the path to row types' labels.

# Documentation

Take a look at my [draft blogpost](doc/BLOG1.md),
I think the main ideas are there,
but the presentation is definitely a work in progress
and probably misses a couple important details as of yet.

(If building the Haddock locally, see <https://github.com/haskell/haddock/issues/900>.)

# Contributing

Please find or create a GitHub Issue on which to discuss your idea;
I'd like to keep the higher-level discussions there
and dig into the details on the PRs.
Thanks very much!
