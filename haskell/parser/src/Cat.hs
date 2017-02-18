{-# LANGUAGE DeriveFunctor, UnicodeSyntax #-}

module Cat where

data Fst a b = Fst (b, a)
  deriving Show

instance Functor (Fst a) where
  fmap f (Fst (y, x)) = Fst (f y, x)

x ∷ Fst Int String
x = Fst ("a", 0)

type FI = Fst Int

newtype Identity a = Identity {runIdentity ∷ a}

instance Functor Identity where
  fmap f (Identity x) = Identity (f x)

newtype Const a b = Const {getConst ∷ a}

-- TODO: Check this
instance Functor (Const a) where
  fmap _ (Const x) = (Const x)

y = (Const 3)  

newtype Compose f g a = Compose {getCompose ∷ f (g a)}

instance (Functor f, Functor g) => Functor (Compose f g) where
  fmap h (Compose x) = Compose (((fmap . fmap) h) x)

--newtype Parser s t = P ([s] → [(t, [s])])
type Parser s t = Compose ((→) [s]) (Compose [] (Fst [s])) t

m ∷ Parser s [t] → Parser s Int
m = fmap length

pLetterA ∷ Parser Char Char
pLetterA = Compose (\xs → Compose (case xs of
                                    ('a' : as) -> [Fst ('a', as)]
                                    _          -> []))
