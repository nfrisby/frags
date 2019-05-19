module Main where

import FragTest

main :: IO ()
main = pure ()

-----

-- tests simplification of SetFrag (DomFrag ...) constraints
test ::
  (
    FragEQ lbl (DomFrag p) ~ 'Nil
  ,
    FragEQ (lbl := a) p ~ 'Nil
  ,
    SetFrag (DomFrag (p :+ lbl := a)) ~ '()
  ,
    SetFrag (p :+ lbl := a) ~ '()
  )
  => Proxy lbl -> Proxy a -> Proxy (p :: Frag (Mapping Nat Symbol)) -> ()
test lbl a p =
    [ pNil , pFragEQ (lbl .= a) p ]
  `seq`
    ()

{-

Without FragEQ (lbl := a) p ~ 'Nil, we are attempting the following.

  have:
      FragEQ lbl (DomFrag p) ~ 'Nil
      SetFrag (DomFrag p)

      SetFrag (FragNE (lbl := a) p)
      SetFrag (FragEQ (lbl := a) p :+ '())   -1 <= p(lbl := a) <= 0

  want:
      FragEQ (lbl := a) p ~ 'Nil

That won't work, because p could for example be

  'Nil :+ lbl := b :- lbl := a

for some b /~ a.

-}
