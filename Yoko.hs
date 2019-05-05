{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -dcore-lint -fplugin=Data.Frag.Plugin #-}

{-# OPTIONS_GHC -Wall -Werror #-}
{-# OPTIONS_GHC -Wwarn=missing-signatures #-}

module Yoko where

import Data.Frag
import Data.Functor.Contravariant (Op(..))
import Dev

-- Type-Indexed Product specializations

nilOp :: TIP 'Nil (Op z)
nilOp = nil

extOp ::
    (SetFrag fr ~ '(),FragEQ a fr ~ 'Nil,KnownFragCard (FragLT a fr))
  =>
    TIP fr (Op z) -> (a -> z) -> TIP (fr :+ a) (Op z)
extOp = \tip f -> tip `ext` Op f

-----

-- An nominal sum of products
data DT = C1 Int | C2 Bool

-- A nominal type for each summand
newtype C1 = MkC1{unC1 :: Int}
  deriving (Show)
newtype C2 = MkC2{unC2 :: Bool}
  deriving (Show)

-- A DT case expression
getOpDT :: TIP ('Nil :+ C1 :+ C2) (Op z) -> DT -> z
getOpDT = \tip dt -> case dt of
  C1 i -> prj tip `getOp` MkC1 i
  C2 b -> prj tip `getOp` MkC2 b

-----

-- Here's an example use of the above

c1case :: C1 -> Bool
c1case (MkC1 i) = i > 0

c2case :: C2 -> Bool
c2case (MkC2 b) = b

-- error:
-- Couldn't match type ‘'Nil :+ C1’ with ‘('Nil :+ C1) :+ C2’
--       Expected type: TIP (('Nil :+ C1) :+ C2) (Op Bool)
--         Actual type: TIP ('Nil :+ C1) (Op Bool)
-- example1 = getOpDT $ nilOp `extOp` c1case

-- error:
-- Couldn't match type ‘'Nil :+ C2’ with ‘('Nil :+ C1) :+ C2’
--       Expected type: TIP (('Nil :+ C1) :+ C2) (Op Bool)
-- Actual type: TIP ('Nil :+ C2) (Op Bool)
-- example2 = getOpDT $ nilOp `extOp` c2case

-- error:
-- Couldn't match type ‘('Nil :+ C1) :+ C1’
--                with ‘('Nil :+ C1) :+ C2’
-- example3 = example8 c1case c1case

-- warning:
-- Top-level binding with no type signature: example4 :: DT -> Bool
example4 = example8 c1case c2case

-- warning:
-- Top-level binding with no type signature: example5 :: DT -> Bool
example5 = example8 c2case c1case
  
-- error:
-- Couldn't match type ‘('Nil :+ C2) :+ C2’
--                with ‘('Nil :+ C1) :+ C2’
-- example6 = example8 c2case c2case

-- warning:
-- Top-level binding with no type signature:
--   example7 :: (KnownFragCard (FragLT a1 ('Nil :+ a2)),
--                (((('Nil :- a1) :- a2) :+ C2) :+ C1) ~ 'Nil,
--                Apart ('OneApart a1 a2) ~ '()) =>
--               () -> (a2 -> z) -> (a1 -> z) -> DT -> z
example7 () = \x y -> getOpDT $ nilOp `extOp` x `extOp` y

-- example7 with a human-written signature
example8 ::
    (
      KnownFragCard (FragLT b ('Nil :+ a))
    ,
      ('Nil :+ a :+ b) ~ ('Nil :+ C1 :+ C2)
    ,
      a /~ b
    )
  =>
    (a -> z) -> (b -> z) -> DT -> z
example8 = example7 ()

-- warning:
-- Couldn't match type ‘((('Nil :- a0) :- a1) :+ C2) :+ C1’
--                with ‘'Nil’
--   arising from a use of ‘example8’
-- The type variables ‘a0’, ‘a1’ are ambiguous
-- example9 = example8 show show

-- warning:
-- Top-level binding with no type signature: example10 :: DT -> String
example10 = example8 (show . unC1) show
example11 = example8 show (show . unC1)
example12 = example8 (show . unC2) show
example13 = example8 show (show . unC2)