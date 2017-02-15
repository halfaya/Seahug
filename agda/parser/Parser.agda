module Parser where

open import Category.Functor
open import Data.List
open import Data.Nat
open import Level

lmap : {ℓ : Level} → {A B : Set ℓ} → (A → B) → (List A → List B)
lmap f []       = []
lmap f (x ∷ xs) = f x ∷ lmap f xs

L : {ℓ : Level} → RawFunctor {ℓ} List
L = record {_<$>_ = lmap}

compose : {ℓ : Level} → {A B C : Set ℓ} → {f : A → B} → {g : B → C} → RawFunctor {ℓ} f → RawFunctor {ℓ} g → RawFunctor {ℓ} (A → C)
compose = ?

a = 1 ∷ 2 ∷ 3 ∷ []
b = lmap ℕ.suc a
