{-# LANGUAGE UnicodeSyntax, GADTs #-}

module Main where

import Prelude hiding (lookup)

data Nat where
  Zero ∷ Nat
  Succ ∷ Nat → Nat
  deriving (Show, Eq)

plus ∷ Nat → Nat → Nat
plus Zero     n = n
plus (Succ m) n = Succ (plus m n)

type Id = Nat

data Expr where
  Var ∷ Id   → Expr
  App ∷ Expr → Expr → Expr
  Lam ∷ Id   → Expr → Expr
  Let ∷ Expr → Expr → Expr
  deriving (Show, Eq)

type TyVar = Nat

data Tau where
  TVar ∷ TyVar → Tau
  Prim ∷ Tau
  TApp ∷ Tau → Tau → Tau
  deriving (Show, Eq)

data Sigma where
  Sigma ∷ [TyVar] → Tau → Sigma
  deriving (Show, Eq)

type Cxt = [(Id, Sigma)]

data Sub where
  Sub ∷ Tau → TyVar → Sub
  deriving (Show, Eq)

type Subs = [Sub]

-- Assume v and all tyvars in t are not present in tau.
subTau ∷ Sub → Tau → Tau
subTau (Sub t v) (TVar v') | v == v'   = t
subTau (Sub t v) (TVar v') | otherwise = TVar v'
subTau s         Prim                  = Prim
subTau s         (TApp t1 t2)          = TApp (subTau s t1) (subTau s t2)

-- Assume v and all tyvars in t are not present in sigma.
subSigma ∷ Sub → Sigma → Sigma
subSigma s (Sigma vs τ) = Sigma vs (subTau s τ)

-- apply subs from last to first
subsTau ∷ Subs → Tau → Tau
subsTau []       τ = τ
subsTau (s : ss) τ = subTau s (subsTau ss τ)

-- apply subs from last to first
subsSigma ∷ Subs → Sigma → Sigma
subsSigma []       σ = σ
subsSigma (s : ss) σ = subSigma s (subsSigma ss σ)

subsCxt ∷ Subs → Cxt → Cxt
subsCxt _  []           = []
subsCxt ss ((x, σ) : γ) = (x, subsSigma ss σ) : subsCxt ss γ

subTau2 ∷ Sub → (Tau, Tau) → (Tau, Tau)
subTau2 s (τ, τ') = (subTau s τ, subTau s τ')

(∘) ∷ Subs → Subs → Subs
(∘) s1 s2 = s1 ++ s2

infixr ∘

-- first argument is number of vars to create
-- second argument is index to start at
fresh ∷ Nat → Nat → [TyVar]
fresh Zero     _ = []
fresh (Succ m) n = n : fresh m (Succ n)

lookup ∷ Cxt → Id → Maybe Sigma
lookup []            _           = Nothing
lookup ((x', σ) : _) x | x' == x = Just σ
lookup (_       : γ) x           = lookup γ x

-- assumes the id can appear at most once
remove ∷ Cxt -> Id -> Cxt
remove []             _           = []
remove ((x', _) : xs) x | x' == x = xs
remove (_ : xs)       x           = remove xs x

len ∷ [a] → Nat
len []       = Zero
len (x : xs) = Succ (len xs)

unify ∷ [(Tau, Tau)] → Maybe Subs
unify [] = Just []
unify (t : τs) = case t of
  (τ, τ') | τ == τ' → unify τs
  (TVar α, τ) → unify (map (subTau2 (Sub τ α)) τs) >>= \s -> Just (s ++ [Sub τ α])
  (τ, TVar α) → unify (map (subTau2 (Sub τ α)) τs) >>= \s -> Just (s ++ [Sub τ α])
  (TApp τ τ', TApp μ μ') → unify ([(τ, μ), (τ', μ')] ++ τs)
  _ → Nothing

-- n is the next available index for a fresh type variable; returns new next index
-- TODO: Handle let.
w ∷ Nat → Cxt → Expr → Maybe (Subs, Tau, Nat)
w n γ e = case e of
  Var x → lookup γ x >>= \(Sigma vs τ) →
                           let l    = len vs
                               vs'  = fresh l n
                               subs = map (\(v, v') → Sub (TVar v') v) (zip vs vs')
                               τ'   = foldr subTau τ subs
                           in Just ([], τ', plus n l)
  App e1 e2 → do
    (s1, τ1, n1) ← w n  γ              e1
    (s2, τ2, n2) ← w n1 (subsCxt s1 γ) e2
    let β = n2
    v            ← unify [(subsTau s2 τ1,  (TApp τ2 (TVar β)))]
    let s = v ∘ s2 ∘ s1
    let τ = subsTau v (TVar β)
    Just (s, τ, Succ n2)
  Lam x e' → let β  = n
                 γ' = (x, Sigma [] (TVar β)) : remove γ x
             in w (Succ n) γ' e' >>= \(subs, τ, n') → Just (subs, subsTau subs (TApp (TVar β) τ), n')
  _     → Nothing

main ∷ IO ()
main = do
  let γ = []
  let e = App (Lam Zero (Var Zero)) (Lam (Succ Zero) (Var (Succ Zero)))
  putStrLn $ show $ w (Succ (Succ Zero)) γ e
