module Cat where

_∘_ : ∀ {ℓ} → {A B C : Set ℓ} → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)

data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a

sym : {A : Set} → {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : {A : Set} → {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

cong : {A B : Set} → {a a′ : A} → (f : A → B) → a ≡ a′ → f a ≡ f a′
cong _ refl = refl

fcong : {A B : Set} → {f g : A → B} → f ≡ g → ((a : A) → (f a ≡ g a))
fcong refl a = refl

postulate
  function-extentionality : {A B : Set} → {f g : A → B} → ((a : A) → (f a ≡ g a)) → f ≡ g

id : (A : Set) → A → A
id A a = a

record Functor : Set₁ where
  constructor F
  field
    F₀     : Set → Set
    F₁     : {A B : Set} → (A → B) → (F₀ A → F₀ B)
    F₁Id   : {A : Set} → {f : A → A} → f ≡ id A → (F₁ f) ≡ id (F₀ A)
    F₁Comp : {A B C : Set} → (g : B → C) → (f : A → B) → (F₁ (g ∘ f)) ≡ ((F₁ g) ∘ (F₁ f))

--  F₁Id   : {A : Set} → {f : A → A} → ((a : A) → f a ≡ a) → ((b : F₀ A) → ((F₁ f) b ≡ b))
--  F₁Comp : (A B C : Set) → (g : B → C) → (f : A → B) → (a : F₀ A) → (F₁ (g ∘ f)) a ≡ ((F₁ g) ∘ (F₁ f)) a

data List (A : Set) : Set where
  []  : List A
  _∷_ : (a : A) → (as : List A) → List A

infix  4 _≡_
infixr 5 _∷_
infixr 9 _∘_

lmap : {A B : Set} → (A → B) → (List A → List B)
lmap _ []       = []
lmap f (x ∷ xs) = f x ∷ lmap f xs

lcong : {A : Set} → {a b : A} → {as bs : List A} → (a ≡ b) → (as ≡ bs) → (a ∷ as ≡ b ∷ bs)
lcong refl refl = refl

lid : {A : Set} → {f : A → A} → ((a : A) → f a ≡ id A a) → ((b : List A) → ((lmap f) b ≡ id (List A) b))
lid _ []       = refl
lid p (a ∷ as) = lcong (p a) (lid p as)

lcomp : {A B C : Set} → (g : B → C) → (f : A → B) → (a : List A) → (lmap (g ∘ f)) a ≡ ((lmap g) ∘ (lmap f)) a
lcomp _ _ []       = refl
lcomp g f (a ∷ as) = lcong refl (lcomp g f as)

listFunctor : Functor
listFunctor = F List
                lmap
                (function-extentionality ∘ lid ∘ fcong)
                (λ g f → function-extentionality (lcomp g f))

_◇_ : Functor → Functor → Functor
(F g₀ g₁ g₁id g₁comp) ◇ (F f₀ f₁ f₁id f₁comp) =
  F (g₀ ∘ f₀)
    (g₁ ∘ f₁)
    (g₁id ∘ f₁id)
    (λ g f → trans (cong g₁ (f₁comp g f)) (g₁comp (f₁ g) (f₁ f)))
