{-# LANGUAGE GADTSyntax, ExplicitForAll #-}

module Meetup where

{-
import Prelude hiding (Maybe(..))

data Maybe ∷ * → * where
  Nothing ∷ ∀ (a ∷ *).     Maybe a
  Just    ∷ ∀ (a ∷ *). a → Maybe a

instance Functor Maybe where
  fmap f Nothing  = Nothing
  fmap f (Just x) = Just (f x)
-}

--data Compose f g a where
--  Compose ∷ f (g a) → Compose f g a

data Compose ∷ (* → *) → (* → *) → * → * where
  Compose ∷ ∀ (f ∷ * → *) (g ∷ * → *) (a ∷ *). f (g a) → Compose f g a

getCompose (Compose x) = x

instance (Functor f, Functor g) => Functor (Compose f g) where
  fmap h (Compose x) = Compose (fmap (fmap h) x)
  
