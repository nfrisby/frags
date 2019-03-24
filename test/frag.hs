{-# LANGUAGE PartialTypeSignatures #-}

{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Main (main) where

import Control.Monad.Trans.Class (lift)
import Data.List.NonEmpty (NonEmpty((:|)))
import Data.Monoid (Any(..),Sum(..))
import Data.Semigroup (Last(..))
import Test.Tasty
import qualified Test.Tasty.HUnit as HUnit
import qualified Test.Tasty.QuickCheck as QC

import qualified Data.Frag.Plugin.Apartness as Apartness
import qualified Data.Frag.Plugin.Class as Class
import qualified Data.Frag.Plugin.Equivalence as Equivalence
import qualified Data.Frag.Plugin.Frag as Frag
import qualified Data.Frag.Plugin.InertSet as InertSet
import Data.Frag.Plugin.TestType
import Data.Frag.Plugin.Types

main :: IO ()
main = defaultMain $ testGroup "frag" [
    testGroup "Unit" [
        frag_unit_tests
      ,
        asym_frag_unit_tests
      ,
        equivalence_unit_tests
      ,
        asym_equivalence_unit_tests
      ,
        sequivalence_unit_tests
      ,
        apartness_unit_tests
      ,
        sapartness_unit_tests
      ,
        sclass_unit_tests
      ,
        inertSet_unit_tests
      ,
        testType_unit_tests
      ]
  ,
     testGroup "QC" [
        frag_qc_tests
      ,
        equivalence_qc_tests
      ]
  ]

-----

nil :: TestType
nil = Con "Nil" []

fragCard :: TestType -> TestType
fragCard = Fun "FragCard" . (:[])

fragEQ :: TestType -> TestType -> TestType
fragEQ b fr = Fun "FragEQ" [b,fr]

fragLT :: TestType -> TestType -> TestType
fragLT b fr = Fun "FragLT" [b,fr]

b0 :: TestType
b0 = Con "0" []

b1 :: TestType
b1 = Con "1" []

b2 :: TestType
b2 = Con "2" []

bT :: TestType -> TestType
bT b = Con "T" [b]

bTrue :: TestType
bTrue = trueTT

bFalse :: TestType
bFalse = falseTT

vx = (MkStr "x",0,False)
vy = (MkStr "y",0,False)

bx :: TestType
bx = case vx of (MkStr s,lvl,fsk) -> Var s lvl fsk

by :: TestType
by = case vy of (MkStr s,lvl,fsk) -> Var s lvl fsk

bz :: TestType
bz = Var "z" 0 False

ba :: TestType
ba = Var "a" 0 False

bb :: TestType
bb = Var "b" 0 False

bc :: TestType
bc = Var "c" 0 False

bd :: TestType
bd = Var "d" 0 False

bp :: TestType
bp = Var "p" 0 False

bq :: TestType
bq = Var "q" 0 False

bL :: TestType -> TestType
bL = Con "L" . (:[])

bR :: TestType -> TestType
bR = Con "R" . (:[])

bP :: TestType -> TestType -> TestType
bP l r = Con "P" [l,r]

bU :: TestType
bU = Frag.envUnit fragEnv

asRoot :: TestType -> Frag TestType TestType
asRoot = MkFrag emptyExt

nIL :: Frag TestType TestType
nIL = asRoot nil

fRAGCard :: TestType -> Frag TestType TestType
fRAGCard fr = asRoot (fragCard fr)

fRAGEQ :: TestType -> TestType -> Frag TestType TestType
fRAGEQ b fr = asRoot (fragEQ b fr)

fRAGLT :: TestType -> TestType -> Frag TestType TestType
fRAGLT b fr = asRoot (fragLT b fr)

newtype SimpleTestType = MkSimpleTestType TestType
  deriving (Show)

instance QC.Arbitrary SimpleTestType where
  arbitrary = fmap MkSimpleTestType $ QC.sized $ \n -> QC.oneof $
    if n < 2 then map pure [b1,b2,bx,by,bTrue,bFalse] else [
        QC.scale ((`div` 2) . pred) $ (\(MkSimpleTestType l) (MkSimpleTestType r) -> Con "P" [l,r]) <$> QC.arbitrary <*> QC.arbitrary
      ,
        QC.scale pred $ (\(MkSimpleTestType x) -> Con "L" [x]) <$> QC.arbitrary
      ,
        QC.scale pred $ (\(MkSimpleTestType x) -> Con "R" [x]) <$> QC.arbitrary
      ]
      
newtype SimpleFrag = MkSimpleFrag (Frag TestType TestType)
  deriving (Show)

instance QC.Arbitrary SimpleFrag where
  arbitrary = fmap MkSimpleFrag $ QC.sized $ \n -> do
    ext_args <- QC.vectorOf n ((,) <$> QC.arbitrary <*> QC.choose (-3,3))
    let
      ext = foldl snoc emptyExt ext_args
      snoc acc (MkSimpleTestType b,count) = insertExt b (mkCount count) acc
    MkSimpleTestType r <- QC.scale (max 1 . (`div` 10)) $ QC.arbitrary
    pure $ MkFrag ext r

newtype SimpleFragEquivalence = MkSimpleFragEquivalence (FragEquivalence TestType TestType)
  deriving (Show)

instance QC.Arbitrary SimpleFragEquivalence where
  arbitrary = fmap MkSimpleFragEquivalence $ do
    MkSimpleFrag (MkFrag ext l) <- QC.arbitrary
    MkSimpleTestType r <- QC.scale (max 1 . (`div` 10)) $ QC.arbitrary
    pure $ MkFragEquivalence (Con "L" [l]) (Con "R" [r]) ext

-----

testGroup_ nm k =
  -- We duplicate each test, switching + and -
  testGroup nm $ k "" (%+) (%-) (%++) (%--) ++ k "[inv] " (%-) (%+) (%--) (%++)

testGroup_asym nm k =
  -- We do not duplicate each test
  testGroup nm $ k "" (%+) (%-) (%++) (%--)

fr %+ b = Fun ":+" [fr,b]
fr %- b = Fun ":-" [fr,b]
MkFrag ext r %++ b = MkFrag (insertExt (b :: TestType) 1 ext) r
MkFrag ext r %-- b = MkFrag (insertExt (b :: TestType) (-1) ext) r

-----

interpretFrag tt = Frag.interpret fragEnv $ Frag.envRawFrag_out fragEnv tt

interpretFragEquivalence l r = Equivalence.interpret eqEnv $ MkRawFragEquivalence l r

simplifyFragEquivalence freq = Equivalence.simplify eqEnv OtherKind freq

interpretApartness pairs = Apartness.interpret (MkRawApartness pairs)

simplifyApartness pairfm = Apartness.simplify apartnessEnv (MkApartness pairfm)

simplifyClass cls = Class.simplify classEnv cls

frag_unit_tests :: TestTree
frag_unit_tests = testGroup_ "Frag" $ \pre plus minus plusplus minusminus ->
  let
    infixl 6 .+, .-, .++, .--
    (.+) = plus; (.-) = minus; (.++) = plusplus; (.--) = minusminus

    each ch nm tt expected = HUnit.testCase (pre ++ nm) $ do
      (Any changed,actual) <- flip runAnyT mempty $ interpretFrag tt
      HUnit.assertEqual "" expected actual
      HUnit.assertEqual "changed" ch changed
    noChange = each False
    change = each True
  in [
    noChange "nil .+ 1 .+ 2"
      (nil .+ b1 .+ b2)
      (nIL .++ b1 .++ b2)
  ,
    change "nil .+ 2 .+ 1"
      (nil .+ b2 .+ b1)
      (nIL .++ b2 .++ b1)
  ,
    noChange "nil .+ 1 .+ 1"
      (nil .+ b1 .+ b1)
      (nIL .++ b1 .++ b1)
  ,
    change "nil .+ 1 .+ 2 :+ 1"
      (nil .+ b1 .+ b2 .+ b1)
      (nIL .++ b1 .++ b2 .++ b1)
  ,
    change "nil .+ 1 .- 1"
      (nil .+ b1 .- b1)
      (nIL .++ b1 .-- b1)
  ,
    change "fragEQ 1 (nil .+ 1 .+ x)"
      (fragEQ b1 (nil .+ b1 .+ bx))
      (fRAGEQ b1 (nil .+ bx) .++ bU)
  ,
    change "fragEQ 1 (nil .+ x .- 1)"
      (fragEQ b1 (nil .+ bx .- b1))
      (fRAGEQ b1 (nil .+ bx) .-- bU)
  ,
    change "fragEQ 1 (nil .+ x .- x)"
      (fragEQ b1 (nil .+ bx .- bx))
      (fRAGEQ b1 nil)
  ,
    change "fragEQ x (nil .+ x)"
      (fragEQ bx (nil .+ bx))
      (fRAGEQ bx nil .++ bU)
  ,
    noChange "fragEQ x (nil .+ 1)"
      (fragEQ bx (nil .+ b1))
      (fRAGEQ bx (nil .+ b1))
  ,
    change "fragLT 1 (nil .+ 1 .+ 2)"
      (fragLT b1 (nil .+ b1 .+ b2))
      (fRAGLT b1 nil)
  ,
    change "fragLT 2 (nil .+ 1 .+ 2)"
      (fragLT b2 (nil .+ b1 .+ b2))
      (fRAGLT b2 nil .++ bU)
  ,
    change "fragLT x (nil .+ x)"
      (fragLT bx (nil .+ bx))
      (fRAGLT bx nil)
  ,
    noChange "fragLT x (nil .+ 1)"
      (fragLT bx (nil .+ b1))
      (fRAGLT bx (nil .+ b1))
  ,
    HUnit.testCase "flattenRawFrag ((nil .+ 1) .+ 2)" $ do
      let
        sgn = if null pre then Pos else Neg
        raw_fr = flattenRawFrag $ MkRawFrag (ExtRawExt NilRawExt sgn b2) $ MkRawFrag (ExtRawExt NilRawExt sgn b1) nil
        expected = nIL .++ b1 .++ b2
      (Any changed,actual) <- flip runAnyT mempty $ Frag.interpret fragEnv raw_fr
      HUnit.assertEqual "" expected actual
      HUnit.assertEqual "changed" False changed
  ]

asym_frag_unit_tests :: TestTree
asym_frag_unit_tests = testGroup_asym "Frag asym" $ \pre plus minus plusplus minusminus ->
  let
    infixl 6 .+, .-, .++, .--
    (.+) = plus; (.-) = minus; (.++) = plusplus; (.--) = minusminus

    each ch nm tt expected = HUnit.testCase (pre ++ nm) $ do
      (Any changed,actual) <- flip runAnyT mempty $ interpretFrag tt
      HUnit.assertEqual "" expected actual
      HUnit.assertEqual "changed" ch changed
    noChange = each False
    change = each True
  in [
    noChange "fsk_{nil .+ 1} .+ 1"
      fsk_nil_plus_1
      (nIL .++ b1)
  ,
    noChange "fsk_{nil .+ 1} .+ 1"
      (fsk_nil_plus_1 .+ b1)
      (nIL .++ b1 .++ b1)
  ,
    change "fsk_{nil .+ 1} .+ 0"
      (fsk_nil_plus_1 .+ b0)
      (nIL .++ b1 .++ b0)
  ,
    noChange "fsk_{nil .+ 1} .+ 2"
      (fsk_nil_plus_1 .+ b2)
      (nIL .++ b1 .++ b2)
  ,
    change "fsk_{nil .+ 1} .+ 2 .+ 1"
      (fsk_nil_plus_1 .+ b2 .+ b1)
      (nIL .++ b1 .++ b2 .++ b1)
  ]

frag_qc_tests :: TestTree
frag_qc_tests = localOption (QC.QuickCheckTests 250) $ testGroup "Frag" [
    QC.testProperty "id" $ \(MkSimpleFrag fr) -> let
      (changed,actual) = flip runAny mempty $ interpretFrag $ Frag.envFrag_inn fragEnv fr
      lbl = case compare n 0 of
        LT -> min (-1) n10
        EQ -> 0
        GT -> max 1 n10
        where
        n10 = div n 10
        n = getCount $ foldMap id $ unExt $ fragExt fr
      in
      QC.collect lbl $
      (changed,actual) QC.=== (mempty,fr)
  ,
    QC.testProperty "raw-forget round-trip" $ \(MkSimpleFrag fr) ->
      forgetFrag fr QC.=== Frag.envRawFrag_out fragEnv (Frag.envFrag_inn fragEnv fr)
  ]

equivalence_qc_tests :: TestTree
equivalence_qc_tests = localOption (QC.QuickCheckTests 250) $ testGroup "Equivalence" [
    QC.testProperty "id" $ \(MkSimpleFragEquivalence (MkFragEquivalence l r ext)) -> let
      (l',r')
        | needSwap l r = (r,l)
        | otherwise = (l,r)
      freq' = MkFragEquivalence l' r' ext
      (changed,actual) = flip runAny mempty $ interpretFragEquivalence
        (MkFrag emptyExt l')
        (MkFrag ext r')
      in
      (changed,actual) QC.=== (mempty,freq')
  ]

testType_unit_tests :: TestTree
testType_unit_tests = testGroup_ "TestType" $ \pre plus minus plusplus minusminus ->
  let
    infixl 6 .+, .-, .++, .--
    (.+) = plus; (.-) = minus; (.++) = plusplus; (.--) = minusminus
  in [
    HUnit.testCase (pre ++ "Key dualizes, so 2 < 1") $ do
      HUnit.assertEqual "" GT $ compareViaFM b1 b2
  ,
    HUnit.testCase (pre ++ "frag_inn 'Nil :+ 1 :+ 2") $ do
      let expected = nil .+ b1 .+ b2
      HUnit.assertEqual "" expected $ Frag.envFrag_inn fragEnv $ nIL .++ b1 .++ b2
  ,
    HUnit.testCase (pre ++ "frag_inn 'Nil :+ 1 :- 2") $ do
      let expected = nil .+ b1 .- b2
      HUnit.assertEqual "" expected $ Frag.envFrag_inn fragEnv $ nIL .++ b1 .-- b2
  ,
    HUnit.testCase (pre ++ "frag_inn 'Nil :+ 1 :+ 2 :+ 2") $ do
      let expected = nil .+ b1 .+ b2 .+ b2
      HUnit.assertEqual "" expected $ Frag.envFrag_inn fragEnv $ nIL .++ b1 .++ b2 .++ b2
  ,
    HUnit.testCase (pre ++ "frag_inn 'Nil :+ 1 :- 2 :- 2") $ do
      let expected = nil .+ b1 .- b2 .- b2
      HUnit.assertEqual "" expected $ Frag.envFrag_inn fragEnv $ nIL .++ b1 .-- b2 .-- b2
  ,
    HUnit.testCase (pre ++ "no occurs check in u") $ do
      let expected = Just $ UnifiableTT $ fmap getLast $ fromListFM [(vx,bL bx)]
      HUnit.assertEqual "" expected $ unifyTT bx (bL bx)
  ,
    HUnit.testCase (pre ++ "bP bx (bP by b1) `u` bP b1 (bP b2 bx)") $ do
      let expected = Just $ UnifiableTT $ fmap getLast $ fromListFM [(vx,b1),(vy,b2)]
      HUnit.assertEqual "" expected $ unifyTT (bP bx (bP by b1)) (bP b1 (bP b2 bx))
  ,
    HUnit.testCase (pre ++ "weird fsk vs x") $ do
      let f = Equivalence.envNeedSwap eqEnv 
      HUnit.assertEqual "" (False,True) (f fsk_weird bx,f bx fsk_weird)
  ]

-----

eq_each :: HUnit.HasCallStack => _ -> _ -> _ -> _ -> _ -> _ -> _ -> _
eq_each ch pre nm l r el er = HUnit.testCase (pre ++ nm) $ do
  (Any changed,actual) <- flip runAnyT mempty $ interpretFragEquivalence l r
  HUnit.assertEqual "" (MkFragEquivalence el (fragRoot er) (fragExt er)) actual
  HUnit.assertEqual "changed" ch changed
eq_noChange :: HUnit.HasCallStack => _ -> _ -> _ -> _ -> _ -> _ -> _
eq_noChange = eq_each False
eq_change :: HUnit.HasCallStack => _ -> _ -> _ -> _ -> _ -> _ -> _
eq_change = eq_each True

equivalence_unit_tests :: TestTree
equivalence_unit_tests = testGroup_ "Equivalence interp" $ \pre plus minus plusplus minusminus ->
  let
    infixl 6 .+, .-, .++, .--
    (.+) = plus; (.-) = minus; (.++) = plusplus; (.--) = minusminus
  in [
    eq_noChange pre "idem nil ~ nil"
      nIL
      nIL
      nil
      nIL
  ,
    eq_noChange pre "ignore swap x ~ nil"
      (asRoot bx)
      nIL
      bx
      nIL
  ,
    eq_noChange pre "ignore swap nil ~ x"
      nIL
      (asRoot bx)
      bx
      nIL
  ,
    eq_noChange pre "x ~ y"
      (asRoot bx)
      (asRoot by)
      bx
      (asRoot by)
  ,
    eq_noChange pre "y ~ x"
      (asRoot by)
      (asRoot bx)
      bx
      (asRoot by)
  ,
    eq_change pre "x .+ 1 ~ nil"
      (asRoot bx .++ b1)
      nIL
      bx
      (nIL .-- b1)
  ,
    eq_change pre "nil ~ x .+ 1"
      nIL
      (asRoot bx .++ b1)
      bx
      (nIL .-- b1)
  ,
    eq_change pre "x .+ 1 ~ y .+ 1"
      (asRoot bx .++ b1)
      (asRoot by .++ b1)
      bx
      (asRoot by)
  ,
    eq_change pre "x .+ 1 ~ y .- 1"
      (asRoot bx .++ b1)
      (asRoot by .-- b1)
      bx
      (asRoot by .-- b1 .-- b1)
  ]

asym_equivalence_unit_tests :: TestTree
asym_equivalence_unit_tests = testGroup_asym "Equivalence interp asymmetric" $ \pre plus minus plusplus minusminus ->
  let
    infixl 6 .+, .-, .++, .--
    (.+) = plus; (.-) = minus; (.++) = plusplus; (.--) = minusminus
  in [
    eq_change pre "invert nil ~ nil .+ 1 .- 2"
      nIL
      (nIL .++ b1 .-- b2)
      nil
      (nIL .-- b1 .++ b2)
  ,
    eq_noChange pre "invert nil ~ nil .- 1 .+ 2"
      nIL
      (nIL .-- b1 .++ b2)
      nil
      (nIL .-- b1 .++ b2)
  ,
    eq_noChange pre "unchanging weird fsk 1"
      (asRoot fsk_weird)
      (asRoot bx)
      bx
      (nIL .++ b1)   -- NB unflattened and swapped, but no changed flag
  ,
    eq_noChange pre "unchanging weird fsk 2"
      (asRoot fsk_weird .++ b1)
      (asRoot bx)
      bx
      (nIL .++ b1 .++ b1)   -- NB unflattened and swapped, but no changed flag
  ,
    eq_change pre "changing weird fsk 3"
      (asRoot fsk_weird .++ b0)
      (asRoot bx)
      bx
      (nIL .++ b1 .++ b0)
  ,
    eq_change pre "changing weird fsk 4"
      (asRoot fsk_weird)
      (asRoot bx .++ b1)
      bx
      nIL
  ]

sequivalence_unit_tests :: TestTree
sequivalence_unit_tests = testGroup_ "Equivalence simpl" $ \pre plus minus plusplus minusminus ->
  let
    infixl 6 .+, .-, .++, .--
    (.+) = plus; (.-) = minus; (.++) = plusplus; (.--) = minusminus

    pair l r   -- polarized equalities are not symmetric wrt + and -
      | null pre = (l,r)
      | otherwise = (r,l)

    pol ext   -- polarized equalities are not symmetric wrt + and -
      | null pre = ext nIL
      | otherwise = let MkFrag e r = ext nIL in MkFrag (invertSign e) r

    each :: HUnit.HasCallStack => Bool -> String -> _ -> _ -> _ -> _
    each ch nm l r expected = HUnit.testCase (pre ++ nm) $ do
      (Any changed,actual) <- flip runAnyT mempty $ simplifyFragEquivalence $ MkFragEquivalence l (fragRoot r) (fragExt r)
      HUnit.assertEqual "" expected actual
      HUnit.assertEqual "changed" ch changed
    contra :: HUnit.HasCallStack => String -> _ -> _ -> _
    contra nm l r = each True ("contra  " ++ nm) l r Contradiction
    derived :: HUnit.HasCallStack => String -> _ -> _ -> _ -> _ -> _ -> _
    derived nm l r derived l' r' = each True ("derived " ++ nm) l r $ OK (derived,MkFragEquivalence l' (fragRoot r') (fragExt r'))
    stuck :: HUnit.HasCallStack => String -> _ -> _ -> _
    stuck nm l r = each False ("stuck   " ++ nm) l r $ OK (emptyDerived,MkFragEquivalence l (fragRoot r) (fragExt r))

  in [
     stuck "nil ~ nil"
      nil
      nIL
  ,
    contra "nil ~ nil .+ x"
      nil
      (nIL .++ bx)
  ,
    derived "x ~ x"
      bx
      (asRoot bx)
      emptyDerived
      nil nIL
  ,
    derived "nil ~ nil .+ x .- y"
      nil
      (nIL .++ bx .-- by)
      emptyDerived{deqs=singletonFM (bx,by) ()}
      nil nIL
  ,
    derived "nil ~ nil .+ L x .- L y .+ R a .- R b"
      nil
      (nIL .++ bL bx .-- bL by .++ bR ba .-- bR bb)
      emptyDerived{deqs=insertFMS (bR ba,bR bb) () $ singletonFM (bL bx,bL by) ()}
      nil nIL
  ,
    stuck "nil ~ nil .- a .+ b .- c .+ d"
      nil
      (pol $ \r -> r .-- ba .++ bb .-- bc .++ bd)
  ,
    derived "nil ~ nil .+ L x .- L y .+ R a .- R b .+ R c .- R d"
      nil
      (nIL .++ bL bx .-- bL by .++ bR ba .-- bR bb .++ bR bc .-- bR bd)
      emptyDerived{deqs=singletonFM (bL bx,bL by) ()}
      nil (pol $ \r -> r .-- bR ba .++ bR bb .-- bR bc .++ bR bd)
  ,
    contra "nil ~ nil .+ 1 .- 2"
      nil
      (nIL .++ b1 .-- b2)
  ,
    contra "nil ~ nil .+ (1,x) .- (2,y)"
      nil
      (nIL .++ bP b1 bx .-- bP b2 by)
  ,
    derived "nil ~ nil .+ (a,b) .- (x,y)"
      nil
      (nIL .++ bP ba bb .-- bP bx by)
      emptyDerived{deqs=singletonFM (bP ba bb,bP bx by) ()}
      nil nIL
  ,
    contra "fragEQ 1 (nil .+ x) ~ nil .- ()"
      (fragEQ b1 (nil .+ bx))
      (nIL .-- bU)
  ,
    derived "fragEQ 1 (nil .+ x) ~ nil"
      (fragEQ b1 (nil .+ bx))
      nIL
      emptyDerived{dneqs=singletonFM (b1,bx) ()}
      nil nIL
  ,
    derived "fragEQ 1 (nil .+ x) ~ nil .+ ()"
      (fragEQ b1 (nil .+ bx))
      (nIL .++ bU)
      emptyDerived{deqs=singletonFM (b1,bx) ()}
      nil nIL
  ,
    contra "fragEQ 1 (nil .+ x) ~ nil .+ () .+ ()"
      (fragEQ b1 (nil .+ bx))
      (nIL .++ bU .++ bU)
  ,
    contra "fragEQ 1 (nil .+ x .+ y) ~ nil .- ()"
      (fragEQ b1 (nil .+ bx .+ by))
      (nIL .-- bU)
  ,
    derived "fragEQ 1 (nil .+ x .+ y) ~ nil"
      (fragEQ b1 (nil .+ bx .+ by))
      nIL
      emptyDerived{dneqs=insertFMS (b1,by) () $ singletonFM (b1,bx) ()}
      nil nIL
  ,
    stuck "fragEQ 1 (nil .+ x .+ y) ~ nil .+ ()"
      (fragEQ b1 (nil .+ bx .+ by))
      (nIL .++ bU)
  ,
    derived "fragEQ 1 (nil .+ x .+ y) ~ nil .+ () .+ ()"
      (fragEQ b1 (nil .+ bx .+ by))
      (nIL .++ bU .++ bU)
      emptyDerived{deqs=insertFMS (b1,by) () $ singletonFM (b1,bx) ()}
      nil nIL
  ,
    contra "fragEQ 1 (nil .+ x .+ y) ~ nil .+ () .+ () .+ ()"
      (fragEQ b1 (nil .+ bx .+ by))
      (nIL .++ bU .++ bU .++ bU)
  ,
    contra "fragEQ 1 (nil .+ x .- y) ~ nil .- () .- ()"
      (fragEQ b1 (nil .+ bx .- by))
      (nIL .-- bU .-- bU)
  ,
    derived "fragEQ 1 (nil .+ x .- y) ~ nil .- ()"
      (fragEQ b1 (nil .+ bx .- by))
      (nIL .-- bU)
      MkDerived{deqs=singletonFM (b1,by) (),dneqs=singletonFM (b1,bx) ()}
      nil nIL
  ,
    stuck "fragEQ 1 (nil .+ x .- y) ~ nil"
      (fragEQ b1 (nil .+ bx .- by))
      nIL
  ,
    derived "fragEQ 1 (nil .+ x .- y) ~ nil .+ ()"
      (fragEQ b1 (nil .+ bx .- by))
      (nIL .++ bU)
      MkDerived{deqs=singletonFM (b1,bx) (),dneqs=singletonFM (b1,by) ()}
      nil nIL
  ,
    contra "fragEQ 1 (nil .+ x .- y) ~ nil .+ () .+ ()"
      (fragEQ b1 (nil .+ bx .- by))
      (nIL .++ bU .++ bU)
  ,
    derived "fragEQ 1 (nil .+ x .+ y .- z) ~ nil .+ () .+ ()"
      (fragEQ b1 (nil .+ bx .+ by .- bz))
      (nIL .++ bU .++ bU)
      MkDerived{
          deqs = insertFMS (b1,by) () $ singletonFM (b1,bx) ()
        ,
          dneqs = singletonFM (b1,bz) ()
        }
      nil nIL
  ,
    contra "fragEQ x (nil .+ y) ~ nil .+ () .+ ()"
      (fragEQ bx (nil .+ by))
      (nIL .++ bU .++ bU)
  ,
    contra "fragEQ x (nil .- y) ~ nil .+ ()"
      (fragEQ bx (nil .- by))
      (nIL .++ bU)
  ,
    contra "fragEQ x (nil .- y) ~ nil .+ ()"
      (fragEQ bx (nil .- by))
      (nIL .++ bU)
  ,
    contra "fragEQ x (nil .+ 1 .+ 2) ~ nil .+ () .+ ()"
      (fragEQ bx (nil .+ b1 .+ b2))
      (nIL .++ bU .++ bU)
  ]

sapartness_unit_tests :: TestTree
sapartness_unit_tests = testGroup_ "Apartness simpl" $ \pre plus minus plusplus minusminus ->
  let
    infixl 6 .+, .-, .++, .--
    (.+) = plus; (.-) = minus; (.++) = plusplus; (.--) = minusminus

    each ch nm pairfm expected = HUnit.testCase (pre ++ nm) $ do
      (Any changed,actual) <- flip runAnyT mempty $ simplifyApartness pairfm
      HUnit.assertEqual "" expected actual
      HUnit.assertEqual "changed" ch changed
    contra nm pairfm = each True ("contra  " ++ nm) pairfm Contradiction
    derived nm pairfm pairfm' = each True ("derived " ++ nm) pairfm $ OK (MkApartness pairfm')
    stuck nm pairfm = each False ("stuck   " ++ nm) pairfm $ OK (MkApartness pairfm)

    triv = singletonFM (Apartness.envTrivial apartnessEnv) ()

  in [
    stuck "trivial"
      triv
  ,
    contra "x /~ x"
      (singletonFM (bx,bx) ())
  ,
    stuck "x /~ y"
      (singletonFM (bx,by) ())
  ,
    stuck "(orient-agnostic) y /~ x"
      (singletonFM (bx,by) ())
  ,
    stuck "z /~ 1"
      (singletonFM (bz,b1) ())
  ,
    stuck "(orient-agnostic) 1 /~ z"
      (singletonFM (bz,b1) ())
  ,
    stuck "x /~ y || 1 /~ z"
      (insertFMS (bx,by) () $ singletonFM (bz,b1) ())
  ,
    derived "L x /~ L y"
      (singletonFM (bL bx,bL by) ())
      (singletonFM (bx,by) ())
  ,
    derived "(x,y) /~ (1,2)"
      (singletonFM (bP bx by,bP b1 b2) ())
      (insertFMS (bx,b1) () $ singletonFM (by,b2) ())
  ,
    derived "L x /~ R y"
      (singletonFM (bL bx,bR by) ())
      triv
  ,
    derived "L x /~ R y || x /~ x"
      (insertFMS (bx,bx) () $ singletonFM (bL bx,bR by) ())
      triv
  ,
    contra "x /~ x || 1 /~ 1"
      (insertFMS (bx,bx) () $ singletonFM (b1,b1) ())
  ]

apartness_unit_tests :: TestTree
apartness_unit_tests = testGroup_ "Apartness interp" $ \pre plus minus plusplus minusminus ->
  let
    infixl 6 .+, .-, .++, .--
    (.+) = plus; (.-) = minus; (.++) = plusplus; (.--) = minusminus

    each ch nm pairs pairsfm = HUnit.testCase (pre ++ nm) $ do
      (Any changed,actual) <- flip runAnyT mempty $ interpretApartness pairs
      HUnit.assertEqual "" (MkApartness pairsfm) actual
      HUnit.assertEqual "changed" ch changed
    change = each True
    noChange = each False

    triv = singletonFM (Apartness.envTrivial apartnessEnv) ()

  in [
    noChange "x /~ y"
      ((bx,by) :| [])
      (singletonFM (bx,by) ())
  ,
    change "y /~ x"
      ((by,bx) :| [])
      (singletonFM (bx,by) ())
  ,
    noChange "x /~ x"
      ((bx,by) :| [])
      (singletonFM (bx,by) ())
  ,
    noChange "x /~ y || y /~ z"
      ((bx,by) :| [(by,bz)])
      (insertFMS (by,bz) () $ singletonFM (bx,by) ())
  ,
    change "y /~ z || x /~ y"
      ((by,bz) :| [(bx,by)])
      (insertFMS (by,bz) () $ singletonFM (bx,by) ())
  ,
    change "x /~ y || x /~ y"
      ((bx,by) :| [(bx,by)])
      (singletonFM (bx,by) ())
  ]    

sclass_unit_tests :: TestTree
sclass_unit_tests = testGroup_asym "Class simpl" $ \pre plus minus plusplus minusminus ->
  let
    infixl 6 .+, .-, .++, .--
    (.+) = plus; (.-) = minus; (.++) = plusplus; (.--) = minusminus

    each ch nm cls expected = HUnit.testCase (pre ++ nm) $ do
      (Any changed,actual) <- flip runAnyT mempty $ simplifyClass cls
      HUnit.assertEqual "" expected actual
      HUnit.assertEqual "changed" ch changed
    contra nm cls = each True ("contra  " ++ nm) cls Contradiction
    derived nm cls eqs neqs cls' = each True ("derived " ++ nm) cls $ OK (MkDerived{deqs=eqs,dneqs=neqs},cls')
    reduced nm cls cls' = each True ("reduced " ++ nm) cls $ OK (emptyDerived,cls')
    stuck nm cls = each False ("stuck   " ++ nm) cls $ OK (emptyDerived,cls)

    triv = singletonFM (Apartness.envTrivial apartnessEnv) ()

  in [
    reduced "knownFragZ decr (p .- x)"
      (KnownFragZ (asRoot bp .-- bx) 100)
      (KnownFragZ (asRoot bp) 99)
  ,
    stuck "knownFragZ stay p"
      (KnownFragZ (asRoot bp) 100)
  ,
    reduced "knownFragZ incr (p .+ x)"
      (KnownFragZ (asRoot bp .++ bx) 100)
      (KnownFragZ (asRoot bp) 101)
  ,
    stuck "setFrag (p .- 1)"
      (SetFrag (asRoot bp .-- b1))
  ,
    stuck "setFrag p"
      (SetFrag (asRoot bp))
  ,
    stuck "setFrag (p .+ 1)"
      (SetFrag (asRoot bp .++ b1))
  ,
    stuck "setFrag (p .+ 1 .+ 1)"
      (SetFrag (asRoot bp .++ b1 .++ b1))
  ,
    contra "setFrag (nil .+ x .+ x)"
      (SetFrag (nIL .++ bx .++ bx))
  ,
    reduced "setFrag (nil .+ 1 .+ 2)"
      (SetFrag (nIL .++ b1 .++ b2))
      (SetFrag nIL)
  ,
    derived "setFrag (nil .+ x .+ y)"
      (SetFrag (nIL .++ bx .++ by))
      emptyFM
      (singletonFM (by,bx) ())
      (SetFrag nIL)
  ,
    derived "setFrag (nil .+ L x .+ L y)"
      (SetFrag (nIL .++ bL bx .++ bL by))
      emptyFM
      (singletonFM (bL by,bL bx) ())   -- SetFrag simplification doesn't unify, but Apartness will
      (SetFrag nIL)
  ,
    derived "setFrag (nil .+ x .+ y .+ z)"
      (SetFrag (nIL .++ bx .++ by .++ bz))
      emptyFM
      (insertFMS (by,bx) () $ insertFMS (bz,bx) () $ singletonFM (bz,by) ())
      (SetFrag nIL)
  ,
    derived "setFrag (nil .+ x .- 1)"
      (SetFrag (nIL .++ bx .-- b1))
      (singletonFM (b1,bx) ())
      emptyFM
      (SetFrag nIL)
  ,
    derived "setFrag (nil .+ x .+ x .- 1)"
      (SetFrag (nIL .++ bx .++ bx .-- b1))
      (singletonFM (b1,bx) ())
      emptyFM
      (SetFrag (nIL .++ bx))
  ,
    derived "setFrag (nil .- x .+ 1)"
      (SetFrag (nIL .-- bx .++ b1))
      (singletonFM (bx,b1) ())
      emptyFM
      (SetFrag nIL)
  ,
    derived "setFrag (nil .- x .+ 1 .+ 1)"
      (SetFrag (nIL .-- bx .++ b1 .++ b1))
      (singletonFM (bx,b1) ())
      emptyFM
      (SetFrag (nIL .++ b1))
  ]

-----

inertSet_unit_tests :: TestTree
inertSet_unit_tests = testGroup_asym "InertSet" $ \pre plus minus plusplus minusminus ->
  let
    infixl 6 .+, .-, .++, .--
    (.+) = plus; (.-) = minus; (.++) = plusplus; (.--) = minusminus

    each ch nm start expected wips = HUnit.testCase (pre ++ (if ch then "" else "[stuck] ") ++ nm) $ do
      (Any changed,actual) <- flip runAnyT mempty $ InertSet.extendInertSet Nothing cacheEnvTT envTT start (wips :: [InertSet.WIP () TestKind TestType])
      HUnit.assertEqual "" expected (fmap fst <$> actual)
      HUnit.assertEqual "changed" ch changed

    each' ch nm start expected wips = HUnit.testCase (pre ++ nm) $ do
      (Any changed,actual) <- flip runAnyT mempty $ InertSet.extendInertSet (Just (\s c -> putStrLn $ s ++ " " ++ show c)) cacheEnvTT envTT start (wips :: [InertSet.WIP () TestKind TestType])
      HUnit.assertEqual "" expected (fmap fst <$> actual)
      HUnit.assertEqual "changed" ch changed

    emptyCache = InertSet.emptyCache emptyFM
    inertSet = flip InertSet.MkInertSet
    emptySet = inertSet emptyCache []

    extApart l r = over InertSet.apartness_table $ alterFM (l,r) (\_ -> Just ())

    extSubst tt fr = case InertSet.envVar_out cacheEnvTT tt of
      Just v -> over InertSet.frag_subst $ alterFM v (\_ -> Just fr)
      Nothing -> error "insertSet_unit_tests.extSubst"

    extMult br intrvl = over InertSet.multiplicity_table $ insertFMS br intrvl

    wip0 = InertSet.MkWIP (Just ((),False))
    wip1 = InertSet.MkWIP (Just ((),True))
    wip_ = InertSet.MkWIP Nothing
    setFrag0 fr = wip0 $ InertSet.ClassCt OtherKind $ SetFrag fr
    setFrag1 fr = wip1 $ InertSet.ClassCt OtherKind $ SetFrag fr

    apart0 l r = wip0 $ InertSet.ApartnessCt $ MkApartness $ singletonFM (l,r) ()
    apart1 l r = wip1 $ InertSet.ApartnessCt $ MkApartness $ singletonFM (l,r) ()
    apart_ l r = wip_ $ InertSet.ApartnessCt $ MkApartness $ singletonFM (l,r) ()
    aparts_ lrs = wip_ $ InertSet.ApartnessCt $ MkApartness $ foldr (\lr -> insertFMS lr ()) emptyFM lrs

    eq0 l r = wip0 $ InertSet.EquivalenceCt OtherKind $ MkFragEquivalence l (fragRoot r) (fragExt r)
    eq1 l r = wip1 $ InertSet.EquivalenceCt OtherKind $ MkFragEquivalence l (fragRoot r) (fragExt r)

    frageq0 b l r = wip0 $ InertSet.EquivalenceCt OtherKind $ MkFragEquivalence (fragEQ b l) (fragRoot r) (fragExt r)
    frageq0' b l r = wip0 $ InertSet.EquivalenceCt OtherKind $ MkFragEquivalence (fragRoot r) (fragEQ b l) (fragExt r)
    frageq1 b l r = wip1 $ InertSet.EquivalenceCt OtherKind $ MkFragEquivalence (fragEQ b l) (fragRoot r) (fragExt r)
    frageq1' b l r = wip1 $ InertSet.EquivalenceCt OtherKind $ MkFragEquivalence (fragRoot r) (fragEQ b l) (fragExt r)
  in [
    each False "empty" emptySet (OK (Right emptySet)) []
  ,
    let
      ct = setFrag0 nIL
    in
    each False "SetFrag 'Nil" emptySet (OK (Right (inertSet emptyCache [ct]))) [ct]
  ,
    let
      ct = setFrag0 $ nIL .++ b1
    in
    each True "SetFrag ('Nil :+ 1)" emptySet (OK (Right (inertSet emptyCache [setFrag1 nIL]))) [ct]
  ,
    let
      ct = eq0 bx (asRoot by .++ b1)
    in
    each False "x ~ y :+ 1" emptySet (OK (Right (inertSet (extSubst bx (asRoot by .++ b1) emptyCache) [ct]))) [ct]
  ,
    let
      ct = eq0 by (asRoot bx .-- b1)
      ct' = eq1 bx (asRoot by .++ b1)
    in
    each True "y ~ x :- 1" emptySet (OK (Right (inertSet (extSubst bx (asRoot by .++ b1) emptyCache) [ct']))) [ct]
  ,
    let
      ct1 = eq0 bx (nIL .++ b1)
      ct2 = setFrag0 (asRoot bx)
      ct2' = setFrag1 nIL
    in
    each True "x ~ 'Nil :+ 1, SetFrag x" emptySet (OK (Right (inertSet (extSubst bx (nIL .++ b1) emptyCache) [ct1,ct2']))) [ct1,ct2]
  ,
    let
      ct1 = frageq0 b1 bx nIL
      ct2 = setFrag0 (asRoot bx .++ b1)
      ct2' = setFrag1 (asRoot bx)
    in
    each True "FragEQ 1 x ~ 'Nil, SetFrag (x :+ 1)" emptySet (OK (Right (inertSet (extMult (bx,b1) (MkCountInterval 0 0) emptyCache) [ct1,ct2']))) [ct1,ct2]
  ,
    let
      ct1 = frageq0 b1 bx nIL
      ct2 = setFrag0 (asRoot bx .++ b1)
      ct2' = setFrag1 (asRoot bx)
    in
    each True "SetFrag (x :+ 1), FragEQ 1 x ~ 'Nil" emptySet (OK (Right (inertSet (extMult (bx,b1) (MkCountInterval 0 0) emptyCache) [ct1,ct2']))) [ct2,ct1]
  ,
    let
      ct1 = frageq0 b1 bx (nIL .-- bU)
      ct2 = setFrag0 (asRoot bx .++ b1)
      ct2' = ct2
    in
    each False "SetFrag (x :+ 1), FragEQ 1 x ~ 'Nil :- '()" emptySet (OK (Right (inertSet (extMult (bx,b1) (MkCountInterval (-1) (-1)) emptyCache) [ct2',ct1]))) [ct2,ct1]
  ,
    let
      ct1 = frageq0 b1 bx (nIL .-- bU)
      ct2 = setFrag0 (asRoot bx .++ b1 .++ b1)
      ct2' = setFrag1 (asRoot bx .++ b1)
    in
    each True "SetFrag (x :+ 1 :+ 1), FragEQ 1 x ~ 'Nil :- '()" emptySet (OK (Right (inertSet (extMult (bx,b1) (MkCountInterval (-1) (-1)) emptyCache) [ct1,ct2']))) [ct2,ct1]
  ,
    -- no change because Class.pop prefers a total multiplicty of 0,
    -- even if that is syntactically larger
    let
      ct1 = frageq0 b1 bx (nIL .++ bU)
      ct2 = setFrag0 (asRoot bx .-- b1)
    in
    each False "SetFrag (x :- 1), FragEQ 1 x ~ 'Nil :+ '()" emptySet (OK (Right (inertSet (extMult (bx,b1) (MkCountInterval 1 1) emptyCache) [ct2,ct1]))) [ct2,ct1]
  ,
    let   -- favor x
      b = bT (fragCard bz)
      ct = eq0 bx (asRoot by .++ b)
    in
    each False "x ~ y :+ T (FragCard z)" emptySet (OK (Right (inertSet (extSubst bx (asRoot by .++ b) emptyCache) [ct]))) [ct]
  ,
    let   -- still favor x even when y fails occurs check
      b = bT (fragCard by)
      ct = eq0 bx (asRoot by .++ b)
    in
    each False "x ~ y :+ T (FragCard y)" emptySet (OK (Right (inertSet (extSubst bx (asRoot by .++ b) emptyCache) [ct]))) [ct]
  ,
    let   -- but use y if x fails occurs check
      b = bT (fragCard bx)
      ct = eq0 bx (asRoot by .++ b)
    in
    each False "x ~ y :+ T (FragCard x)" emptySet (OK (Right (inertSet (extSubst by (asRoot bx .-- b) emptyCache) [ct]))) [ct]
  ,
    let   -- or use neither if both fail occurs check
      bTx = bT (fragCard bx)
      bTy = bT (fragCard by)
      ct = eq0 bx (asRoot by .++ bTx .++ bTy)
    in
    each False "x ~ y :+ T (FragCard x) :+ T (FragCard y)" emptySet (OK (Right (inertSet emptyCache [ct]))) [ct]
  ,
    let
      ct1 = eq0 bx (asRoot by .++ b1)
      ct2 = eq0 by (asRoot bz .++ b1)
      cache' = extSubst bx (asRoot bz .++ b1 .++ b1) $ extSubst by (asRoot bz .++ b1) $ emptyCache
    in
    each False "x ~ y :+ 1, y ~ z :+ 1" emptySet (OK (Right (inertSet cache' [ct1,ct2]))) [ct1,ct2]
  ,
    let
      ct1 = eq0 bx (asRoot by .++ b1)
      ct1' = eq1 bx (asRoot bz)
      ct2 = eq0 by (asRoot bz .-- b1)
      ct2' = ct2
      cache' = extSubst by (asRoot bz .-- b1) emptyCache   -- no x := z mapping, left to GHC since no extension
    in
    each True "x ~ y :+ 1, y ~ z :- 1" emptySet (OK (Right (inertSet cache' [ct2',ct1']))) [ct1,ct2]
  ,
    let   -- like previous, but ct2 changes
      ct1 = eq0 bx (asRoot by .++ b1)
      ct1' = eq1 bx (asRoot bz)
      ct2 = eq0 bx (asRoot bz)
      ct2' = eq1 by (asRoot bz .-- b1)
      cache' = extSubst by (asRoot bz .-- b1) emptyCache   -- no x := z mapping, left to GHC since no extension
    in
    each True "x ~ y :+ 1, x ~ z" emptySet (OK (Right (inertSet cache' [ct2',ct1']))) [ct1,ct2]
  ,
    let
      ct = apart0 bc bx
      cache' = extApart bc bx emptyCache
    in
    each False "c /~ x" emptySet (OK (Right (inertSet cache' [ct]))) [ct]
  ,
    let   -- reorientation does not count for Apartness constraints (important?)
      ct = apart0 bx bc
      ct' = apart0 bc bx
      cache' = extApart bc bx emptyCache
    in
    each False "x /~ c" emptySet (OK (Right (inertSet cache' [ct']))) [ct]
  ,
    let
      ct1 = apart0 bc bx
      ct2 = frageq0 bx (nil .+ ba .+ bb .+ bc) (nIL .++ bU)
      ct1' = ct1
      ct2' = frageq1 bx (nil .+ ba .+ bb) (nIL .++ bU)
      cache' = extApart bc bx emptyCache
    in
    each True "c /~ x, 1 ~ FragEQ x ('Nil :+ a :+ b :+ c)" emptySet (OK (Right (inertSet cache' [ct1',ct2']))) [ct1,ct2]
  ,
    let
      ct1 = apart0 bc bx
      ct2 = frageq0 (bT bx) (nil .+ bT ba .+ bT bb .+ bT bc) (nIL .++ bU)
      ct1' = ct1
      ct2' = frageq1 (bT bx) (nil .+ bT ba .+ bT bb) (nIL .++ bU)
      cache' = extApart bc bx emptyCache
    in
    each True "c /~ x, 1 ~ FragEQ (T x) ('Nil :+ T a :+ T b :+ T c)" emptySet (OK (Right (inertSet cache' [ct1',ct2']))) [ct1,ct2]
  ,
    let
      ct1 = apart0 (bT bc) (bT bx)
      ct2 = frageq0 bx (nil .+ ba .+ bb .+ bc) (nIL .++ bU)
      ct1' = apart1 bc bx
      ct2' = frageq1 bx (nil .+ ba .+ bb) (nIL .++ bU)
      cache' = extApart bc bx emptyCache
    in
    each True "T c /~ T x, 1 ~ FragEQ x ('Nil :+ a :+ b :+ c)" emptySet (OK (Right (inertSet cache' [ct1',ct2']))) [ct1,ct2]
  ,
    let
      ct = frageq0 bx (nil .+ by) nIL
      ct' = eq1 nil nIL
      ct'' = apart_ bx by
      cache' = extApart bx by emptyCache
    in
    each True "0 ~ FragEQ x ('Nil :+ y)" emptySet (OK (Right (inertSet cache' [ct',ct'']))) [ct]
  ,
    let
      ct = frageq0 (bP ba bx) (nil .+ bP bb by) nIL
      ct' = eq1 nil nIL
      ct'' = aparts_ [(ba,bb),(bx,by)]
      cache' = emptyCache
    in
    each True "0 ~ FragEQ (P a x) ('Nil :+ P b y)" emptySet (OK (Right (inertSet cache' [ct',ct'']))) [ct]
  ,
    let
      ct = frageq0 (bP ba bx) (nil .+ bP bb bx) nIL
      cts' = [eq1 nil nIL,apart_ ba bb]
      cache' = extApart ba bb emptyCache
    in
    each True "0 ~ FragEQ (P a x) ('Nil :+ P b x)" emptySet (OK (Right (inertSet cache' cts'))) [ct]
  ,
    let
      ct = setFrag0 (nIL .++ ba .++ bb .++ bc)
      ct' = setFrag1 nIL
      cts' = [apart_ ba bc,ct',apart_ bb bc,apart_ ba bb]
      cache' = extApart ba bb $ extApart ba bc $ extApart bb bc $ emptyCache
    in
    each True "SetFrag ('Nil :+ a :+ b :+ c)" emptySet (OK (Right (inertSet cache' cts'))) [ct]
  ]
