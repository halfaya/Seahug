module Cat where

_∘_ : ∀ {ℓ} → {A B C : Set ℓ} → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)

data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a

sym : {A : Set} → {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : {A : Set} → {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

record Functor : Set₁ where
  constructor F
  field
    F₀     : Set → Set
    F₁     : {A B : Set} → (A → B) → (F₀ A → F₀ B)
    F₁Id   : {A : Set} → {f : A → A} → ((a : A) → f a ≡ a) → ((b : F₀ A) → ((F₁ f) b ≡ b))
    F₁Comp : (A B C : Set) → (g : B → C) → (f : A → B) → (a : F₀ A) → (F₁ (g ∘ f)) a ≡ ((F₁ g) ∘ (F₁ f)) a

data List (A : Set) : Set where
  []  : List A
  _∷_ : (a : A) → (as : List A) → List A

infix  4 _≡_
infixr 5 _∷_

lmap : {A B : Set} → (A → B) → (List A → List B)
lmap f []       = []
lmap f (x ∷ xs) = f x ∷ lmap f xs

lcong : {A : Set} → {a b : A} → {as bs : List A} → (a ≡ b) → (as ≡ bs) → (a ∷ as ≡ b ∷ bs)
lcong refl refl = refl

lid : {A : Set} → {f : A → A} → ((a : A) → f a ≡ a) → ((b : List A) → ((lmap f) b ≡ b))
lid p []       = refl
lid p (a ∷ as) = lcong (p a) (lid p as)

lcomp : (A B C : Set) → (g : B → C) → (f : A → B) → (a : List A) → (lmap (g ∘ f)) a ≡ ((lmap g) ∘ (lmap f)) a
lcomp A B C _ _ []       = refl
lcomp A B C g f (a ∷ as) = lcong refl (lcomp A B C g f as)

listFunctor : Functor
listFunctor = F List lmap lid lcomp

_◇_ : Functor → Functor → Functor
(F g₀ g₁ g₁id g₁comp) ◇ (F f₀ f₁ f₁id f₁comp) =
  F (g₀ ∘ f₀)
    (g₁ ∘ f₁)
    (g₁id ∘ f₁id)
    (λ A B C g f a → let x = g₁comp (f₀ A) (f₀ B) (f₀ C) (f₁ g) (f₁ f) a in {!!})
