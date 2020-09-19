{-# OPTIONS --without-K --safe #-}

module Context where

open import Type
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)

infixl 60 _▹_
infixl 60 _▹<:_
infixl 60 _▹T<:_
infixl 60 _▹F<:_

data Context : Set where
  -- \emptyset
  ∅ : Context
  -- \t6
  _▹_ : Context → Type → Context
  _▹<:_ : Context → Type → Context
  _▹T<:_ : Context → ℕ → Context
  _▹F<:_ : Context → ℕ → Context

-- is type in context relation

-- \in
data _∈_ : Type → Context → Set where
  Z∈ : ∀ {T Γ}
    → T ∈ Γ ▹ T
  S∈ : ∀ {T Γ U}
    → T ∈ Γ
    → T ∈ Γ ▹ U
  S∈<: : ∀ {T Γ U}
    → T ∈ Γ
    → T ∈ Γ ▹<: U
  S∈T<: : ∀ {T Γ n}
    → T ∈ Γ
    → T ∈ Γ ▹T<: n
  S∈F<: : ∀ {T Γ n}
    → T ∈ Γ
    → T ∈ Γ ▹F<: n

-- is subtype in context relation

data <:_∈_ : Type → Context → Set where
  Z<: : ∀ {T Γ}
    → <: T ∈ Γ ▹<: T
  S<: : ∀ {T Γ U}
    → <: T ∈ Γ
    → <: T ∈ Γ ▹ U
  S<:∈ : ∀ {T Γ U}
    → <: T ∈ Γ
    → <: T ∈ Γ ▹<: U
  S<:T<: : ∀ {T Γ n}
    → <: T ∈ Γ
    → <: T ∈ Γ ▹T<: n
  S<:F<: : ∀ {T Γ n}
    → <: T ∈ Γ
    → <: T ∈ Γ ▹F<: n

-- is True <: in context relation

data T<:_∈_ : ℕ → Context → Set where
  ZT<: : ∀ {Γ n}
    → T<: n ∈ Γ ▹T<: n
  ST<: : ∀ {Γ n T}
    → T<: n ∈ Γ
    → T<: n ∈ Γ ▹<: T
  ST<:∈ : ∀ {Γ n T}
    → T<: n ∈ Γ
    → T<: n ∈ Γ ▹<: T
  ST<:T : ∀ {Γ n m}
    → T<: n ∈ Γ
    → T<: n ∈ Γ ▹T<: m
  SF<:F : ∀ {Γ n m}
    → T<: n ∈ Γ
    → T<: n ∈ Γ ▹F<: m

-- is False <: in context relation

data F<:_∈_ : ℕ → Context → Set where
  ZF<: : ∀ {Γ n}
    → F<: n ∈ Γ ▹F<: n
  SF<: : ∀ {Γ n T}
    → F<: n ∈ Γ
    → F<: n ∈ Γ ▹<: T
  SF<:∈ : ∀ {Γ n T}
    → F<: n ∈ Γ
    → F<: n ∈ Γ ▹<: T
  SF<:T : ∀ {Γ n m}
    → F<: n ∈ Γ
    → F<: n ∈ Γ ▹T<: m
  SF<:F : ∀ {Γ n m}
    → F<: n ∈ Γ
    → F<: n ∈ Γ ▹F<: m

ext-∈ : ∀ {Γ Δ}
  → (∀ {A} → A ∈ Γ → A ∈ Δ)
  → (∀ {A B} → A ∈ Γ ▹ B → A ∈ Δ ▹ B)
ext-∈ f Z∈ = Z∈
ext-∈ f (S∈ x) = S∈ (f x)

{-
rename-∈ : ∀ {Γ Δ}
  → (∀ {A} → A ∈ Γ → A ∈ Δ)
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename-∈ f x = ?
-}
