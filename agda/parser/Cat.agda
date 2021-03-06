module Cat where

infix  4 _≡_
infixr 5 _∷_
infixr 9 _∘_ _◇_
infixr 2 _×_

id : ∀ {ℓ} → (A : Set ℓ) → A → A
id A a = a

-- function composition
_∘_ : ∀ {ℓ} → {A B C : Set ℓ} → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)

-- propositional equality
data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a

sym : {A : Set} → {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : {A : Set} → {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

cong : {A B : Set} → {a a′ : A} → (f : A → B) → a ≡ a′ → f a ≡ f a′
cong _ refl = refl

fcong : {A B : Set} → {f g : A → B} → f ≡ g → (a : A) → (f a ≡ g a)
fcong refl a = refl

-- function extensionality
postulate
  function-extensionality : {A B : Set} → {f g : A → B} → ((a : A) → (f a ≡ g a)) → f ≡ g

-- functors
record Functor : Set₁ where
  constructor F
  field
    F₀     : Set → Set
    F₁     : {A B : Set} → (A → B) → (F₀ A → F₀ B)
    F₁Id   : {A : Set} → (F₁ (id A)) ≡ id (F₀ A)
    F₁Comp : {A B C : Set} → (g : B → C) → (f : A → B) → (F₁ (g ∘ f)) ≡ ((F₁ g) ∘ (F₁ f))

--  F₁Id   : {A : Set} → {f : A → A} → ((a : A) → f a ≡ a) → ((b : F₀ A) → ((F₁ f) b ≡ b))
--  F₁Comp : (A B C : Set) → (g : B → C) → (f : A → B) → (a : F₀ A) → (F₁ (g ∘ f)) a ≡ ((F₁ g) ∘ (F₁ f)) a

open Functor

_◇_ : Functor → Functor → Functor
(F g₀ g₁ g₁id g₁comp) ◇ (F f₀ f₁ f₁id f₁comp) =
  F (g₀ ∘ f₀)
    (g₁ ∘ f₁)
    (trans (cong g₁ f₁id) g₁id)
    (λ g f → trans (cong g₁ (f₁comp g f)) (g₁comp (f₁ g) (f₁ f)))

-- identity functor
idFunctor : Functor
idFunctor = F (id Set)
              (λ f → f)
              refl
              (λ _ _ → refl)

-- constant functor
constantFunctor : Set → Functor
constantFunctor A = F (λ _   → A)
                      (λ _   → id A)
                      refl
                      (λ _ _ → refl)

-- lists
data List (A : Set) : Set where
  []  : List A
  _∷_ : (a : A) → (as : List A) → List A

lmap : {A B : Set} → (A → B) → (List A → List B)
lmap _ []       = []
lmap f (x ∷ xs) = f x ∷ lmap f xs

lcong : {A : Set} → {a b : A} → {as bs : List A} → (a ≡ b) → (as ≡ bs) → (a ∷ as ≡ b ∷ bs)
lcong refl refl = refl

lid : {A : Set} → (a : List A) → (lmap (id A)) a ≡ id (List A) a
lid []       = refl
lid (a ∷ as) = lcong refl (lid as)

lcomp : {A B C : Set} → (g : B → C) → (f : A → B) → (a : List A) → (lmap (g ∘ f)) a ≡ ((lmap g) ∘ (lmap f)) a
lcomp _ _ []       = refl
lcomp g f (_ ∷ as) = lcong refl (lcomp g f as)

listFunctor : Functor
listFunctor = F List
                lmap
                (function-extensionality lid)
                (λ g f → function-extensionality (lcomp g f))

-- products
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    π₁ : A
    π₂ : B

pmap : {X A B : Set} → (A → B) → (X × A → X × B)
pmap f (x , a) = (x , f a)

pcong : {A B : Set} → {a₁ a₂ : A} → {b₁ b₂ : B} → (a₁ ≡ a₂) → (b₁ ≡ b₂) → (a₁ , b₁) ≡ (a₂ , b₂)
pcong refl refl = refl

pid : {X A : Set} → ((p : X × A) → ((pmap (id A)) p ≡ id (X × A) p))
pid (x , a) = pcong refl refl

pcomp : {X A B C : Set} → (g : B → C) → (f : A → B) → (a : X × A) → (pmap (g ∘ f)) a ≡ ((pmap g) ∘ (pmap f)) a
pcomp g f (x , a) = refl

productFunctor : Set → Functor
productFunctor A = F (_×_ A)
                  pmap
                  (function-extensionality pid)
                  (λ g f -> function-extensionality (pcomp g f))

-- examples
listProductFunctor : Set → Functor
listProductFunctor A = listFunctor ◇ productFunctor A

data Bool : Set where
  true  : Bool
  false : Bool

cbf = F₀ (constantFunctor Bool)
lpf = F₀ (listProductFunctor Bool)
