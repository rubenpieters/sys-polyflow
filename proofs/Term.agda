module Term where

open import Type
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)

infix 50 ′_
infix 50 B′_
infixl 40 _∙_
infixl 40 _[_]
infix 35 if_then_else
infix 32 _===_
infix 30 ƛ_⋯>_∶_
infix 30 Λ<:_⋯>_

data Term : Set where
  -- variables
  ′_ : ℕ → Term
  -- bool literals
  B′_ : Bool → Term
  -- if expr
  if_then_else : Term → Term → Term → Term
  -- function abstraction
  ƛ_⋯>_∶_ : Type → Term → Type → Term
  -- application
  _∙_ : Term → Term → Term
  -- type abstraction
  Λ<:_⋯>_ : Type → Term → Term
  -- type application
  _[_] : Term → Type → Term
  -- equality check
  _===_ : Term → Term → Term
