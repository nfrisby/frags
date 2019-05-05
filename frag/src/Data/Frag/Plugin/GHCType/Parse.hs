{-# LANGUAGE Rank2Types #-}

module Data.Frag.Plugin.GHCType.Parse where

import Control.Applicative ((<|>))
import Data.Monoid (Any(..))
import qualified Outputable as O
import TcType (TcKind,TcType)
import TcRnTypes (Ct)

import qualified Data.Frag.Plugin.Apartness as Apartness
import qualified Data.Frag.Plugin.Equivalence as Equivalence
import qualified Data.Frag.Plugin.Frag as Frag
import qualified Data.Frag.Plugin.GHCType as GHCType
import Data.Frag.Plugin.InertSet (WIP(..))
import qualified Data.Frag.Plugin.InertSet as InertSet
import Data.Frag.Plugin.GHCType.Fsk (Unflat)
import Data.Frag.Plugin.Lookups (E)
import qualified Data.Frag.Plugin.Types as Types

mkWIP ::
    Monad m
  =>
    (forall a. Types.AnyT m a -> m (Any,a))
  ->
    E
  ->
    Unflat
  ->
    Ct
  ->
    m (Maybe (WIP Ct TcKind TcType))
mkWIP run env unflat c = do
  let
    fragEnv = GHCType.fragEnv env unflat

    apartnessCt = flip fmap (GHCType.apartness_out env unflat c) $ \pairs -> do
      Types.printM $ O.text "mkWIP ApartnessCt"
      InertSet.ApartnessCt <$> Apartness.interpret (Types.MkRawApartness pairs)

    eqCt = flip fmap (GHCType.fragEquivalence_candidate_out env c) $ \(k,l,r) -> do
      Types.printM $ O.text "mkWIP EquivalenceCt"
      lfr <- Frag.interpret fragEnv l
      rfr <- Frag.interpret fragEnv r
      eq <- Equivalence.interpret (GHCType.eqEnv env unflat) (Types.MkRawFragEquivalence lfr rfr)
      pure $ InertSet.EquivalenceCt k eq

    knownFragZCt = flip fmap (GHCType.knownFragZ_out env c) $ \(k,fr) -> do
      Types.printM $ O.text "mkWIP KnownFragCard"
      fr' <- Frag.interpret fragEnv fr
      pure $ InertSet.ClassCt k (Types.KnownFragZ fr' 0)

    setFragCt = flip fmap (GHCType.setFrag_out env unflat c) $ \(k,fr) -> do
      Types.printM $ O.text "mkWIP SetFrag"
      fr' <- Frag.interpret fragEnv fr
      pure $ InertSet.ClassCt k (Types.SetFrag fr')

  let
    mmwip =
        apartnessCt
      <|>
        eqCt
      <|>
        knownFragZCt
      <|>
        setFragCt
  case mmwip of
    Just m -> (\(Any hit,ct) -> Just $ MkWIP (Just (c,hit)) ct) <$> run m
    Nothing -> pure Nothing
