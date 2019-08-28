module Alg where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym)
open import Data.String using (String; _≟_)
open import Data.Bool using (Bool; true; false)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (∃; ∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Level
open import Data.String.Properties
open import Map <-strictTotalOrder-≈

Id : Set
Id = String

Label : Set
Label = String

data Type : Set where
  number : Type
  boolean : Type
  L'_ : Label → Type
  M'_ : Map Type → Type
  _[_] : Type → Id → Type
--  _∨_ : Type → Type → Type

f1 : Type
f1 = let
  map1 : Map Type
  map1 = insert "t" number (singleton "f" boolean)
  in M' map1

f2 : Type
f2 = f1 [ "t" ]

data Sing {c : Level} {A : Set c} : A → Set c where
  sing : (x : A) -> Sing x

getSimplifiedIndexedAccessType : ∀ {objectType indexType}
  → (type : Sing ((M' objectType) [ indexType ]))
  → Maybe Type
getSimplifiedIndexedAccessType (sing ((M' objectType) [ indexType ])) = let
  resolved : Maybe Type
  resolved = lookup indexType objectType
  in resolved

test = getSimplifiedIndexedAccessType (sing f2)

{-
symbols:
⟨ = \<
⟩ = \>
-}
