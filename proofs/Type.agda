{-# OPTIONS --without-K --safe #-}

module Type where

open import Data.Nat using (ℕ; zero; suc)

infix 55 _∨_
infix 50 _⇒_
infix 50 ′′_
infix 40 A<:_∶_
infix 40 [T=_,F=_][_]

data Type : Set where
  TTrue : Type
  TFalse : Type
  _⇒_ : Type → Type → Type
  ′′_ : ℕ → Type
  A<:_∶_ : Type → Type → Type
  Top : Type
  _∨_ : Type → Type → Type
  [T=_,F=_][_] : Type → Type → Type → Type

TBool : Type
TBool = TTrue ∨ TFalse
