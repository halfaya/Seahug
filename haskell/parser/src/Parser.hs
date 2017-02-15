{-# LANGUAGE ExplicitForAll #-}

module Parser where

(∘) ∷ ∀ a b c. (b → c) → (a → b) → (a → c)
f ∘ g = f . g

newtype Parser s t = P ([s] → [(t, [s])])

unP ∷ ∀ s t. Parser s t → [s] → [(t, [s])]
unP (P p) = p

pLettera ∷ Parser Char Char
pLettera = P f
  where f ('a' : s) = [('a', s)]
        f _         = []

pSym ∷ Eq s => s -> Parser s s
pSym c = P f
  where f (x : xs) | x == c = [(x, xs)]
        f _                 = []

evalParser ∷ (Parser s t) → [s] → [(t, [s])]
evalParser (P f) xs = f xs

pReturn ∷ a → Parser s a
pReturn c = P f
  where f xs = [(c, xs)]

pFail ∷ ∀ s t. Parser s t
pFail = P (const [])

instance Functor (Parser s) where
  fmap f (P p) = P (map (\(y, zs) → (f y, zs)) ∘ p)

instance Applicative (Parser s) where
  pure = pReturn
  P p1 <*> P p2 = P (\xs → [(f a, zs) | (f, ys) ← p1 xs, (a, zs) ← p2 ys])

pString_aa ∷ Parser Char [Char]
pString_aa = pReturn (\x y → x : [y]) <*> pLettera <*> pLettera

(<|>) ∷ Parser s a → Parser s a → Parser s a
P p <|> P q = P (\x → p x ++ q x)

infixr 3 <|>

parens ∷ Parser Char Int
parens = pReturn 0 <|> (\_ b _ d → max (b + 1) d) <$> pSym '(' <*> parens <*> pSym ')' <*> parens
