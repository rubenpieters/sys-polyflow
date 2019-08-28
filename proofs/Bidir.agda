module Bidir where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym)
open import Data.String using (String; _≟_)
open import Data.Bool using (Bool; true; false)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (∃; ∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

Id : Set
Id = String

-- -------------------------------------
-- TYPES

infix 55 _∨_
infix 51 ′′_
infix 50 _⇨_
infix 40 Φ_<:_∶_

data Type : Set where
  TTrue : Type
  TFalse : Type
  _⇨_ : Type → Type → Type
  Top : Type
  ′′_ : Id → Type
  Φ_<:_∶_ : Id → Type → Type → Type
  _∨_ : Type → Type → Type

TBool : Type
TBool = TTrue ∨ TFalse

-- -------------------------------------

-- -------------------------------------
-- TERMS

infix 50 ′_
infix 50 B′_
infixl 45 _↓_
infixl 40 _∙_
infixl 40 _[_]
infix 35 if_then_else
infix 30 ƛ_⋯>_
infix 30 Λ_<:_⋯>_

data Term : Set where
  -- variables
  ′_ : Id → Term
  -- application
  _∙_ : Term → Term → Term
  -- type application
  _[_] : Term → Type → Term
  -- annotation
  _↓_ : Term → Type → Term
  -- bool literals
  B′_ : Bool → Term
  -- if expr
  if_then_else : Term → Term → Term → Term
  -- function abstraction
  ƛ_⋯>_ : Id → Term → Term
  -- type abstraction
  Λ_<:_⋯>_ : Id → Type → Term → Term

-- -------------------------------------

-- -------------------------------------
-- CONTEXT

-- definition

infixl 50 _,_∶_
infixl 50 _,_<:_

data Context : Set where
  ∅ : Context
  _,_∶_ : Context → Id → Type → Context
  _,_<:_ : Context → Id → Type → Context

-- has-type-in-context relation

data _∶_∈_ : Id → Type → Context → Set where
  Z: : ∀ {x T Γ}
    → x ∶ T ∈ Γ , x ∶ T
  S: : ∀ {x T Γ y U}
    → x ≢ y
    → x ∶ T ∈ Γ
    → x ∶ T ∈ Γ , y ∶ U
  S:-Skip<: : ∀ {x A Γ S T}
    → x ∶ A ∈ Γ
    → x ∶ A ∈ Γ , S <: T

-- is-subtype-in-context relation

data _<:_∈_ : Id → Type → Context → Set where
  Z<: : ∀ {Γ X T}
    → X <: T ∈ Γ , X <: T
  S<: : ∀ {Γ X T Y U}
    → X ≢ Y
    → X <: T ∈ Γ
    → X <: T ∈ Γ , Y <: U
  S<:-Skip: : ∀ {Γ X T y U}
    → X <: T ∈ Γ
    → X <: T ∈ Γ , y ∶ U

-- -------------------------------------

-- -------------------------------------
-- SUBTYPING RELATION

data _⊢_<:_ : Context → Type → Type → Set where
  S-Refl : ∀ {Γ S}
    → Γ ⊢ S <: S
  S-Trans : ∀ {Γ S U T}
    → Γ ⊢ S <: U
    → Γ ⊢ U <: T
    → Γ ⊢ S <: T
  S-Top : ∀ {Γ S}
    → Γ ⊢ S <: Top
  S-TVar : ∀ {Γ X T}
    → X <: T ∈ Γ
    → Γ ⊢ ′′ X <: T
  S-Arrow : ∀ {Γ S₁ S₂ T₁ T₂}
    → Γ ⊢ T₁ <: S₁
    → Γ ⊢ S₂ <: T₂
    → Γ ⊢ (S₁ ⇨ S₂) <: (T₁ ⇨ T₂)
  S-All : ∀ {Γ X U S T}
    → Γ , X <: U ⊢ S <: T
    → Γ ⊢ (Φ X <: U ∶ S) <: (Φ X <: U ∶ T)
  S-UnionL : ∀ {Γ T A B}
    → Γ ⊢ T <: A
    → Γ ⊢ T <: A ∨ B
  S-UnionR : ∀ {Γ T A B}
    → Γ ⊢ T <: B
    → Γ ⊢ T <: A ∨ B

-- inversion

inversion-<:-var : ∀ {Γ S X}
  → Γ ⊢ S <: ′′ X
  → ∃[ Y ](S ≡ ′′ Y)
inversion-<:-var {X = X} (S-Refl) = (X , refl)
inversion-<:-var (S-Trans S<:U U<:′′X) with inversion-<:-var U<:′′X
... | (_ , refl) = inversion-<:-var S<:U
inversion-<:-var (S-TVar {X = X} _) = (X , refl)

inversion-<:-true : ∀ {Γ S}
  → Γ ⊢ S <: TTrue
  → (∃ λ X → S ≡ ′′ X) ⊎ S ≡ TTrue
inversion-<:-true S-Refl = inj₂ refl
inversion-<:-true (S-Trans S<:U U<:TTrue) with inversion-<:-true U<:TTrue
... | inj₁ (_ , refl) = inj₁ (inversion-<:-var S<:U)
... | inj₂ refl = inversion-<:-true S<:U
inversion-<:-true (S-TVar {X = X} X<:TTrue) = inj₁ (X , refl)

inversion-<:-false : ∀ {Γ S}
  → Γ ⊢ S <: TFalse
  → (∃ λ X → S ≡ ′′ X) ⊎ S ≡ TFalse
inversion-<:-false S-Refl = inj₂ refl
inversion-<:-false (S-Trans S<:U U<:TFalse) with inversion-<:-false U<:TFalse
... | inj₁ (_ , refl) = inj₁ (inversion-<:-var S<:U)
... | inj₂ refl = inversion-<:-false S<:U
inversion-<:-false (S-TVar {X = X} X<:TFalse) = inj₁ (X , refl)

inversion-<:-bool : ∀ {Γ S}
  → Γ ⊢ S <: TBool
  → (∃ λ X → S ≡ ′′ X) ⊎ S ≡ TBool ⊎ S ≡ TTrue ⊎ S ≡ TFalse
inversion-<:-bool (S-Refl) = inj₂ (inj₁ refl)
inversion-<:-bool (S-Trans S<:U U<:TBool) with inversion-<:-bool U<:TBool
... | inj₁ (_ , refl) = inj₁ (inversion-<:-var S<:U)
... | inj₂ (inj₁ refl) = inversion-<:-bool S<:U
... | inj₂ (inj₂ (inj₁ refl)) with inversion-<:-true S<:U
...   | inj₁ (X , refl) = inj₁ (X , refl)
...   | inj₂ refl = inj₂ (inj₂ (inj₁ refl))
inversion-<:-bool (S-Trans S<:U U<:TBool) | inj₂ (inj₂ (inj₂ refl)) with inversion-<:-false S<:U
...   | inj₁ (X , refl) = inj₁ (X , refl)
...   | inj₂ refl = inj₂ (inj₂ (inj₂ refl))
inversion-<:-bool (S-TVar {X = X} _) = inj₁ (X , refl)
inversion-<:-bool (S-UnionL S<:True) with inversion-<:-true S<:True
... | inj₁ (X , refl) = inj₁ (X , refl)
... | inj₂ refl = inj₂ (inj₂ (inj₁ refl))
inversion-<:-bool (S-UnionR S<:False) with inversion-<:-false S<:False
... | inj₁ (X , refl) = inj₁ (X , refl)
... | inj₂ refl = inj₂ (inj₂ (inj₂ refl))

inversion-<:-abs : ∀ {Γ S T₁ T₂}
  → Γ ⊢ S <: T₁ ⇨ T₂
  → ∃[ X ](S ≡ ′′ X) ⊎ ∃[ S₁ ](∃[ S₂ ](Γ ⊢ T₁ <: S₁ × Γ ⊢ S₂ <: T₂ × S ≡ S₁ ⇨ S₂))
inversion-<:-abs {T₁ = T₁} {T₂ = T₂} (S-Refl) = inj₂ (T₁ , T₂ , S-Refl , S-Refl , refl)
inversion-<:-abs (S-Trans S<:U U<:T₁⇨T₂) with inversion-<:-abs U<:T₁⇨T₂
... | inj₁ (_ , refl) = inj₁ (inversion-<:-var S<:U)
... | inj₂ (U₁ , U₂ , T₁<:U₁ , U₂<:T₂ , refl) with inversion-<:-abs S<:U
...   | inj₁ (X , refl) = inj₁ (X , refl)
...   | inj₂ (S₁ , S₂ , U₁<:S₁ , S₂<:U₂ , refl) = inj₂ (S₁ , S₂ , S-Trans T₁<:U₁ U₁<:S₁ , S-Trans S₂<:U₂ U₂<:T₂ , refl)
inversion-<:-abs (S-TVar {X = X} _) = inj₁ (X , refl)
inversion-<:-abs (S-Arrow {S₁ = S₁} {S₂ = S₂} T₁<:S₁ S₂<:T₂) = inj₂ (S₁ , S₂ , T₁<:S₁ , S₂<:T₂ , refl)

inversion-<:-forall : ∀ {Γ S U₁ T₂ X}
  → Γ ⊢ S <: Φ X <: U₁ ∶ T₂
  → ∃[ X ](S ≡ ′′ X) ⊎ ∃[ S₂ ](Γ , X <: U₁ ⊢ S₂ <: T₂ × S ≡ Φ X <: U₁ ∶ S₂)
inversion-<:-forall {T₂ = T₂} (S-Refl) = inj₂ (T₂ , S-Refl , refl)
inversion-<:-forall (S-Trans S<:U U<:Φ) with inversion-<:-forall U<:Φ
... | inj₁ (_ , refl) = inj₁ (inversion-<:-var S<:U)
... | inj₂ (U₂ , (U₂<:T₂ , refl)) with inversion-<:-forall S<:U
...  | inj₁ (X , refl) = inj₁ (X , refl)
...  | inj₂ (S₂ , (S₂<:U₂ , refl)) = inj₂ (S₂ , S-Trans S₂<:U₂ U₂<:T₂ , refl)
inversion-<:-forall (S-TVar {X = X} _) = inj₁ (X , refl)
inversion-<:-forall (S-All {S = S} S<:T) = inj₂ (S , S<:T , refl)

inversion-<:-or : ∀ {Γ S A B}
  → Γ ⊢ S <: A ∨ B
  → ∃[ X ](S ≡ ′′ X) ⊎ S ≡ A ∨ B ⊎ Γ ⊢ S <: A ⊎ Γ ⊢ S <: B
inversion-<:-or S-Refl = inj₂ (inj₁ refl)
inversion-<:-or (S-Trans S<:U U<:A∨B) with inversion-<:-or U<:A∨B
... | inj₁ (_ , refl) = inj₁ (inversion-<:-var S<:U)
... | inj₂ (inj₂ (inj₁ U<:A)) = inj₂ (inj₂ (inj₁ (S-Trans S<:U U<:A)))
... | inj₂ (inj₂ (inj₂ U<:B)) = inj₂ (inj₂ (inj₂ (S-Trans S<:U U<:B)))
... | inj₂ (inj₁ refl) with inversion-<:-or S<:U
...   | inj₁ (X , refl) = inj₁ (X , refl)
...   | inj₂ (inj₂ (inj₁ S<:A)) = inj₂ (inj₂ (inj₁ S<:A))
...   | inj₂ (inj₂ (inj₂ S<:B)) = inj₂ (inj₂ (inj₂ S<:B))
...   | inj₂ (inj₁ refl) = inj₂ (inj₁ refl)
inversion-<:-or (S-TVar {X = X} _) = inj₁ (X , refl)
inversion-<:-or (S-UnionL T<:A) = inj₂ (inj₂ (inj₁ T<:A))
inversion-<:-or (S-UnionR T<:B) = inj₂ (inj₂ (inj₂ T<:B))

-- imp subtyping

imp-TTrue<:⇨ : ∀ {Γ A B}
  → Γ ⊢ TTrue <: A ⇨ B
  → ⊥
imp-TTrue<:⇨ (S-Trans x y) with inversion-<:-abs y
... | inj₂ (a , b , c , d , refl) = imp-TTrue<:⇨ x
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()

imp-TTrue<:TFalse : ∀ {Γ}
  → Γ ⊢ TTrue <: TFalse
  → ⊥
imp-TTrue<:TFalse (S-Trans x y) with inversion-<:-false y
... | inj₂ refl = imp-TTrue<:TFalse x
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()

imp-TTrue<:′′ : ∀ {Γ X}
  → Γ ⊢ TTrue <: ′′ X
  → ⊥
imp-TTrue<:′′ (S-Trans x y) with inversion-<:-var y
... | (_ , refl) = imp-TTrue<:′′ x

imp-TTrue<:Φ : ∀ {Γ X T U}
  → Γ ⊢ TTrue <: Φ X <: T ∶ U
  → ⊥
imp-TTrue<:Φ (S-Trans x y) with inversion-<:-forall y
... | inj₂ (a , b , refl) = imp-TTrue<:Φ x
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()

imp-TTrue<:∨ : ∀ {Γ A B}
  → Γ ⊢ TTrue <: A ∨ B
  → ¬ Γ ⊢ TTrue <: A
  → ¬ Γ ⊢ TTrue <: B
  → ⊥
imp-TTrue<:∨ (S-Trans x y) ¬True<:A ¬True<:B with inversion-<:-or y
... | inj₂ (inj₁ refl) = imp-TTrue<:∨ x ¬True<:A ¬True<:B
... | inj₂ (inj₂ (inj₁ U<:A)) = ¬True<:A (S-Trans x U<:A)
... | inj₂ (inj₂ (inj₂ U<:B)) = ¬True<:B (S-Trans x U<:B)
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()
imp-TTrue<:∨ (S-UnionL T<:A) ¬True<:A ¬True<:B = ¬True<:A T<:A
imp-TTrue<:∨ (S-UnionR T<:B) ¬True<:A ¬True<:B = ¬True<:B T<:B

imp-TFalse<:⇨ : ∀ {Γ A B}
  → Γ ⊢ TFalse <: A ⇨ B
  → ⊥
imp-TFalse<:⇨ (S-Trans x y) with inversion-<:-abs y
... | inj₂ (a , b , c , d , refl) = imp-TFalse<:⇨ x
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()

imp-TFalse<:TTrue : ∀ {Γ}
  → Γ ⊢ TFalse <: TTrue
  → ⊥
imp-TFalse<:TTrue (S-Trans x y) with inversion-<:-true y
... | inj₂ refl = imp-TFalse<:TTrue x
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()

imp-TFalse<:′′ : ∀ {Γ X}
  → Γ ⊢ TFalse <: ′′ X
  → ⊥
imp-TFalse<:′′ (S-Trans x y) with inversion-<:-var y
... | (_ , refl) = imp-TFalse<:′′ x

imp-TFalse<:Φ : ∀ {Γ X T U}
  → Γ ⊢ TFalse <: Φ X <: T ∶ U
  → ⊥
imp-TFalse<:Φ (S-Trans x y) with inversion-<:-forall y
... | inj₂ (a , b , refl) = imp-TFalse<:Φ x
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()

imp-TFalse<:∨ : ∀ {Γ A B}
  → Γ ⊢ TFalse <: A ∨ B
  → ¬ Γ ⊢ TFalse <: A
  → ¬ Γ ⊢ TFalse <: B
  → ⊥
imp-TFalse<:∨ (S-Trans x y) ¬False<:A ¬False<:B with inversion-<:-or y
... | inj₂ (inj₁ refl) = imp-TFalse<:∨ x ¬False<:A ¬False<:B
... | inj₂ (inj₂ (inj₁ U<:A)) = ¬False<:A (S-Trans x U<:A)
... | inj₂ (inj₂ (inj₂ U<:B)) = ¬False<:B (S-Trans x U<:B)
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()
imp-TFalse<:∨ (S-UnionL T<:A) ¬False<:A ¬False<:B = ¬False<:A T<:A
imp-TFalse<:∨ (S-UnionR T<:B) ¬False<:A ¬False<:B = ¬False<:B T<:B

imp-⇨<:TTrue : ∀ {Γ A B}
  → Γ ⊢ A ⇨ B <: TTrue
  → ⊥
imp-⇨<:TTrue (S-Trans x y) with inversion-<:-true y
... | inj₂ refl = imp-⇨<:TTrue x
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()

imp-⇨<:TFalse : ∀ {Γ A B}
  → Γ ⊢ A ⇨ B <: TFalse
  → ⊥
imp-⇨<:TFalse (S-Trans x y) with inversion-<:-false y
... | inj₂ refl = imp-⇨<:TFalse x
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()

imp-⇨<:′′ : ∀ {Γ A B X}
  → Γ ⊢ A ⇨ B <: ′′ X
  → ⊥
imp-⇨<:′′ (S-Trans x y) with inversion-<:-var y
... | (_ , refl) = imp-⇨<:′′ x

imp-⇨<:Φ : ∀ {Γ A B X T U}
  → Γ ⊢ A ⇨ B <: Φ X <: T ∶ U
  → ⊥
imp-⇨<:Φ (S-Trans x y) with inversion-<:-forall y
... | inj₂ (a , b , refl) = imp-⇨<:Φ x
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()

imp-⇨<:∨ : ∀ {Γ A B L R}
  → Γ ⊢ A ⇨ B <: L ∨ R
  → ¬ Γ ⊢ A ⇨ B <: L
  → ¬ Γ ⊢ A ⇨ B <: R
  → ⊥
imp-⇨<:∨ (S-Trans x y) ¬⇨<:A ¬⇨<:B with inversion-<:-or y
... | inj₂ (inj₁ refl) = imp-⇨<:∨ x ¬⇨<:A ¬⇨<:B
... | inj₂ (inj₂ (inj₁ U<:A)) = ¬⇨<:A (S-Trans x U<:A)
... | inj₂ (inj₂ (inj₂ U<:B)) = ¬⇨<:B (S-Trans x U<:B)
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()
imp-⇨<:∨ (S-UnionL T<:A) ¬⇨<:A ¬⇨<:B = ¬⇨<:A T<:A
imp-⇨<:∨ (S-UnionR T<:B) ¬⇨<:A ¬⇨<:B = ¬⇨<:B T<:B

imp-Top<:TTrue : ∀ {Γ}
  → Γ ⊢ Top <: TTrue
  → ⊥
imp-Top<:TTrue (S-Trans x y) with inversion-<:-true y
... | inj₂ refl = imp-Top<:TTrue x
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()

imp-Top<:TFalse : ∀ {Γ}
  → Γ ⊢ Top <: TFalse
  → ⊥
imp-Top<:TFalse (S-Trans x y) with inversion-<:-false y
... | inj₂ refl = imp-Top<:TFalse x
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()

imp-Top<:⇨ : ∀ {Γ A B}
  → Γ ⊢ Top <: A ⇨ B
  → ⊥
imp-Top<:⇨ (S-Trans x y) with inversion-<:-abs y
... | inj₂ (a , b , c , d , refl) = imp-Top<:⇨ x
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()

imp-Top<:′′ : ∀ {Γ X}
  → Γ ⊢ Top <: ′′ X
  → ⊥
imp-Top<:′′ (S-Trans x y) with inversion-<:-var y
... | (_ , refl) = imp-Top<:′′ x

imp-Top<:Φ : ∀ {Γ X T U}
  → Γ ⊢ Top <: Φ X <: T ∶ U
  → ⊥
imp-Top<:Φ (S-Trans x y) with inversion-<:-forall y
... | inj₂ (a , b , refl) = imp-Top<:Φ x
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()

imp-Top<:∨ : ∀ {Γ L R}
  → Γ ⊢ Top <: L ∨ R
  → ¬ Γ ⊢ Top <: L
  → ¬ Γ ⊢ Top <: R
  → ⊥
imp-Top<:∨ (S-Trans x y) ¬Top<:A ¬Top<:B with inversion-<:-or y
... | inj₂ (inj₁ refl) = imp-Top<:∨ x ¬Top<:A ¬Top<:B
... | inj₂ (inj₂ (inj₁ U<:A)) = ¬Top<:A (S-Trans x U<:A)
... | inj₂ (inj₂ (inj₂ U<:B)) = ¬Top<:B (S-Trans x U<:B)
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()
imp-Top<:∨ (S-UnionL T<:A) ¬Top<:A ¬Top<:B = ¬Top<:A T<:A
imp-Top<:∨ (S-UnionR T<:B) ¬Top<:A ¬Top<:B = ¬Top<:B T<:B

imp-Φ<:TTrue : ∀ {Γ X T U}
  → Γ ⊢ Φ X <: T ∶ U <: TTrue
  → ⊥
imp-Φ<:TTrue (S-Trans x y) with inversion-<:-true y
... | inj₂ refl = imp-Φ<:TTrue x
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()

imp-Φ<:TFalse : ∀ {Γ X T U}
  → Γ ⊢ Φ X <: T ∶ U <: TFalse
  → ⊥
imp-Φ<:TFalse (S-Trans x y) with inversion-<:-false y
... | inj₂ refl = imp-Φ<:TFalse x
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()

imp-Φ<:⇨ : ∀ {Γ X T U A B}
  → Γ ⊢ (Φ X <: T ∶ U) <: (A ⇨ B)
  → ⊥
imp-Φ<:⇨ (S-Trans x y) with inversion-<:-abs y
... | inj₂ (a , b , c , d , refl) = imp-Φ<:⇨ x
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()

imp-Φ<:′′ : ∀ {Γ X T U Y}
  → Γ ⊢ (Φ X <: T ∶ U) <: ′′ Y
  → ⊥
imp-Φ<:′′ (S-Trans x y) with inversion-<:-var y
... | (_ , refl) = imp-Φ<:′′ x

imp-Φ<:∨ : ∀ {Γ X T U L R}
  → Γ ⊢ (Φ X <: T ∶ U) <: L ∨ R
  → ¬ Γ ⊢ (Φ X <: T ∶ U) <: L
  → ¬ Γ ⊢ (Φ X <: T ∶ U) <: R
  → ⊥
imp-Φ<:∨ (S-Trans x y) ¬Φ<:A ¬Φ<:B with inversion-<:-or y
... | inj₂ (inj₁ refl) = imp-Φ<:∨ x ¬Φ<:A ¬Φ<:B
... | inj₂ (inj₂ (inj₁ U<:A)) = ¬Φ<:A (S-Trans x U<:A)
... | inj₂ (inj₂ (inj₂ U<:B)) = ¬Φ<:B (S-Trans x U<:B)
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()
imp-Φ<:∨ (S-UnionL T<:A) ¬Φ<:A ¬Φ<:B = ¬Φ<:A T<:A
imp-Φ<:∨ (S-UnionR T<:B) ¬Φ<:A ¬Φ<:B = ¬Φ<:B T<:B

imp-∨<:TTrue : ∀ {Γ L R}
  → Γ ⊢ L ∨ R <: TTrue
  → ⊥
imp-∨<:TTrue (S-Trans x y) with inversion-<:-true y
... | inj₂ refl = imp-∨<:TTrue x
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()

imp-∨<:TFalse : ∀ {Γ L R}
  → Γ ⊢ L ∨ R <: TFalse
  → ⊥
imp-∨<:TFalse (S-Trans x y) with inversion-<:-false y
... | inj₂ refl = imp-∨<:TFalse x
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()

imp-∨<:⇨ : ∀ {Γ L R A B}
  → Γ ⊢ L ∨ R <: (A ⇨ B)
  → ⊥
imp-∨<:⇨ (S-Trans x y) with inversion-<:-abs y
... | inj₂ (a , b , c , d , refl) = imp-∨<:⇨ x
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()

imp-∨<:′′ : ∀ {Γ L R X}
  → Γ ⊢ L ∨ R <: ′′ X
  → ⊥
imp-∨<:′′ (S-Trans x y) with inversion-<:-var y
... | (_ , refl) = imp-∨<:′′ x

imp-∨<:Φ : ∀ {Γ L R X T U}
  → Γ ⊢ L ∨ R <: Φ X <: T ∶ U
  → ⊥
imp-∨<:Φ (S-Trans x y) with inversion-<:-forall y
... | inj₂ (a , b , refl) = imp-∨<:Φ x
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()

-- -------------------------------------

-- -------------------------------------
-- TYPING

-- type substitution

infix 50 _[_τ=_]

_[_τ=_] : Type → Id → Type → Type
(′′ x) [ y τ= s ] with x ≟ y
... | yes _ = s
... | no _ = ′′ x
TTrue [ y τ= s ] = TTrue
TFalse [ y τ= s ] = TFalse
(A ⇨ B) [ y τ= s ] = (A [ y τ= s ]) ⇨ (B [ y τ= s ])
(Φ X <: T ∶ U) [ y τ= s ] = Φ X <: (T [ y τ= s ]) ∶ U [ y τ= s ]
Top [ y τ= s ] = Top
(A ∨ B) [ y τ= s ] = (A [ y τ= s ]) ∨ (B [ y τ= s ])

data _⊢_⇒_ : Context → Term → Type → Set
data _⊢_⇐_ : Context → Term → Type → Set

data _⊢_⇒_ where
  BT-Var : ∀ {Γ x A}
    → x ∶ A ∈ Γ
    → Γ ⊢ ′ x ⇒ A
  BT-True : ∀ {Γ}
    → Γ ⊢ B′ true ⇒ TTrue
  BT-False : ∀ {Γ}
    → Γ ⊢ B′ false ⇒ TFalse
  BT-App : ∀ {Γ t₁ t₂ A B}
    → Γ ⊢ t₁ ⇒ A ⇨ B
    → Γ ⊢ t₂ ⇐ A
    → Γ ⊢ t₁ ∙ t₂ ⇒ B
  BT-TApp : ∀ {Γ t₁ X T U Y}
    → Γ ⊢ t₁ ⇒ (Φ X <: T ∶ U)
    → Γ ⊢ Y <: T
    → Γ ⊢ t₁ [ Y ] ⇒ U [ X τ= Y ]
  BT-Ann : ∀ {Γ t T}
    → Γ ⊢ t ⇐ T
    → Γ ⊢ t ↓ T ⇒ T

data _⊢_⇐_ where
  BT-If : ∀ {Γ t₁ t₂ t₃ T}
    → Γ ⊢ t₁ ⇐ TBool
    → Γ ⊢ t₂ ⇐ T
    → Γ ⊢ t₃ ⇐ T
    → Γ ⊢ if t₁ then t₂ else t₃ ⇐ T
  BT-Abs : ∀ {Γ x t A B}
    → Γ , x ∶ A ⊢ t ⇐ B
    → Γ ⊢ (ƛ x ⋯> t) ⇐ (A ⇨ B)
  BT-TAbs : ∀ {Γ X T t U}
    → Γ , X <: T ⊢ t ⇐ U
    → Γ ⊢ (Λ X <: T ⋯> t) ⇐ (Φ X <: T ∶ U)
  BT-CheckInfer : ∀ {Γ t A B}
    → Γ ⊢ t ⇒ A
    → A ≡ B
    → Γ ⊢ t ⇐ B
  BT-Sub : ∀ {Γ t A B}
    → Γ ⊢ t ⇒ A
    → Γ ⊢ A <: B
    → Γ ⊢ t ⇐ B

-- -------------------------------------

_≟Tp_ : (A : Type) → (B : Type) → Dec (A ≡ B)
TTrue ≟Tp TTrue = yes refl
TTrue ≟Tp TFalse = no λ()
TTrue ≟Tp (A ⇨ B) = no λ()
TTrue ≟Tp Top = no λ()
TTrue ≟Tp (′′ x) = no λ()
TTrue ≟Tp (Φ x <: t ∶ t₁) = no λ()
TTrue ≟Tp (A ∨ B) = no λ()
TFalse ≟Tp TFalse = yes refl
TFalse ≟Tp TTrue = no λ()
TFalse ≟Tp (A ⇨ B) = no λ()
TFalse ≟Tp Top = no λ()
TFalse ≟Tp (′′ x) = no λ()
TFalse ≟Tp (Φ x <: t ∶ t₁) = no λ()
TFalse ≟Tp (A ∨ B) = no λ()
(A ⇨ B) ≟Tp TTrue = no λ()
(A ⇨ B) ≟Tp TFalse = no λ()
(A ⇨ B) ≟Tp Top = no λ()
(A ⇨ B) ≟Tp (′′ X) = no λ()
(A ⇨ B) ≟Tp (Φ X <: T ∶ U) = no λ()
(A ⇨ B) ≟Tp (_ ∨ _) = no λ()
(A₁ ⇨ B₁) ≟Tp (A₂ ⇨ B₂) with A₁ ≟Tp A₂ | B₁ ≟Tp B₂
... | no A₁≢A₂ | _ = no  λ{refl → A₁≢A₂ refl}
... | yes _    | no B₁≢B₂ = no λ{refl → B₁≢B₂ refl}
... | yes refl | yes refl = yes refl
Top ≟Tp Top = yes refl
Top ≟Tp TTrue = no λ()
Top ≟Tp TFalse = no λ()
Top ≟Tp (A ⇨ B) = no λ()
Top ≟Tp (′′ X) = no λ()
Top ≟Tp (Φ X <: T ∶ U) = no λ()
Top ≟Tp (A ∨ B) = no λ()
(′′ X₁) ≟Tp (′′ X₂) with X₁ ≟ X₂
... | yes refl = yes refl
... | no X₁≠X₂ = no (λ{refl → X₁≠X₂ refl})
(′′ X) ≟Tp TTrue = no λ()
(′′ X) ≟Tp TFalse = no λ()
(′′ X) ≟Tp (A ⇨ B) = no λ()
(′′ X) ≟Tp Top = no λ()
(′′ X) ≟Tp (Φ Y <: T ∶ U) = no λ()
(′′ X) ≟Tp (A ∨ B) = no λ()
(Φ X <: T ∶ U) ≟Tp TTrue = no λ()
(Φ X <: T ∶ U) ≟Tp TFalse = no λ()
(Φ X <: T ∶ U) ≟Tp (A ⇨ B) = no λ()
(Φ X <: T ∶ U) ≟Tp Top = no λ()
(Φ X <: T ∶ U) ≟Tp (′′ _) = no λ()
(Φ X <: T ∶ U) ≟Tp (A ∨ B) = no λ()
(Φ X₁ <: T₁ ∶ U₁) ≟Tp (Φ X₂ <: T₂ ∶ U₂) with X₁ ≟ X₂ | T₁ ≟Tp T₂ | U₁ ≟Tp U₂
... | no X₁≠X₂ | _ | _ = no λ{refl → X₁≠X₂ refl}
... | yes _ | no T₁≠T₂ | _ = no λ{refl → T₁≠T₂ refl}
... | yes _ | yes _ | no U₁≠U₂ = no λ{refl → U₁≠U₂ refl}
... | yes refl | yes refl | yes refl = yes refl
(A ∨ B) ≟Tp TTrue = no λ()
(A ∨ B) ≟Tp TFalse = no λ()
(A ∨ B) ≟Tp (_ ⇨ _) = no λ()
(A ∨ B) ≟Tp Top = no λ()
(A ∨ B) ≟Tp (′′ X) = no λ()
(A ∨ B) ≟Tp (Φ X <: T ∶ U) = no λ()
(A₁ ∨ B₁) ≟Tp (A₂ ∨ B₂) with A₁ ≟Tp A₂ | B₁ ≟Tp B₂
... | yes refl | yes refl = yes refl
... | no A₁≠A₂ | _ = no λ{refl → A₁≠A₂ refl}
... | _ | no B₁≠B₂ = no λ{refl → B₁≠B₂ refl}

TTrue≠⇨ : ∀ {A B}
  → TTrue ≢ A ⇨ B
TTrue≠⇨ ()

TTrue≠Φ : ∀ {X T U}
  → TTrue ≢ Φ X <: T ∶ U
TTrue≠Φ ()

TTrue≠Top : TTrue ≢ Top
TTrue≠Top ()

TTrue≠′′ : ∀ {X}
  → TTrue ≢ ′′ X
TTrue≠′′ ()

TFalse≠⇨ : ∀ {A B}
  → TFalse ≢ A ⇨ B
TFalse≠⇨ ()

TFalse≠Φ : ∀ {X T U}
  → TFalse ≢ Φ X <: T ∶ U
TFalse≠Φ ()

TFalse≠Top : TBool ≢ Top
TFalse≠Top ()

TFalse≠′′ : ∀ {X}
  → TFalse ≢ ′′ X
TFalse≠′′ ()

TBool≠⇨ : ∀ {A B}
  → TBool ≢ A ⇨ B
TBool≠⇨ ()

TBool≠Φ : ∀ {X T U}
  → TBool ≢ Φ X <: T ∶ U
TBool≠Φ ()

TBool≠Top : TBool ≢ Top
TBool≠Top ()

TBool≠′′ : ∀ {X}
  → TBool ≢ ′′ X
TBool≠′′ ()

Top≠⇨ : ∀ {A B}
  → Top ≢ A ⇨ B
Top≠⇨ ()

Top≠′′ : ∀ {X}
  → Top ≢ ′′ X
Top≠′′ ()

Top≠Φ : ∀ {X T U}
  → Top ≢ Φ X <: T ∶ U
Top≠Φ ()

⇨≠′′ : ∀ {A B X}
  → A ⇨ B ≢ ′′ X
⇨≠′′ ()

⇨≠Φ : ∀ {A B X T U}
  → A ⇨ B ≢ Φ X <: T ∶ U
⇨≠Φ ()

⇨≠∨ : ∀ {A B C D}
  → A ⇨ B ≢ C ∨ D
⇨≠∨ ()

Φ≠′′ : ∀ {X T U Y}
  → Φ X <: T ∶ U ≢ ′′ Y
Φ≠′′ ()

Φ≠∨ : ∀ {X T U A B}
  → Φ X <: T ∶ U ≢ A ∨ B
Φ≠∨ ()

∨≠′′ : ∀ {A B X}
  → A ∨ B ≢ ′′ X
∨≠′′ ()

uniq-∈ : ∀ {x A B Γ}
  → x ∶ A ∈ Γ
  → x ∶ B ∈ Γ
  → A ≡ B
uniq-∈ Z: Z: = refl
uniq-∈ Z: (S: x≠x _) = ⊥-elim (x≠x refl)
uniq-∈ (S: x≠x _) Z: = ⊥-elim (x≠x refl)
uniq-∈ (S: _ x:A∈Γ) (S: _ x:B∈Γ) = uniq-∈ x:A∈Γ x:B∈Γ
uniq-∈ (S:-Skip<: x:A∈Γ) (S:-Skip<: x:B∈Γ) = uniq-∈ x:A∈Γ x:B∈Γ

uniq-<:∈ : ∀ {X A B Γ}
  → X <: A ∈ Γ
  → X <: B ∈ Γ
  → A ≡ B
uniq-<:∈ Z<: Z<: = refl
uniq-<:∈ Z<: (S<: X≠X _) = ⊥-elim (X≠X refl)
uniq-<:∈ (S<: X≠X _) Z<: = ⊥-elim (X≠X refl)
uniq-<:∈ (S<: _ X<:A∈Γ) (S<: _ X<:B∈Γ) = uniq-<:∈ X<:A∈Γ X<:B∈Γ
uniq-<:∈ (S<:-Skip: X<:A∈Γ) (S<:-Skip: X<:B∈Γ) = uniq-<:∈ X<:A∈Γ X<:B∈Γ

uniq-⇒ : ∀ {Γ t A B}
  → Γ ⊢ t ⇒ A
  → Γ ⊢ t ⇒ B
  → A ≡ B
uniq-⇒ (BT-Var x:A∈Γ) (BT-Var x:B∈Γ) = uniq-∈ x:A∈Γ x:B∈Γ
uniq-⇒ BT-True BT-True = refl
uniq-⇒ BT-False BT-False = refl
uniq-⇒ (BT-App t₁⇒A₁⇨B₁ _) (BT-App t₁⇒A₂⇨B₂ _) with uniq-⇒ t₁⇒A₁⇨B₁ t₁⇒A₂⇨B₂
... | refl = refl
uniq-⇒ (BT-Ann _) (BT-Ann _) = refl
uniq-⇒ (BT-TApp t⇒Φ₁ Y<:T₁) (BT-TApp t⇒Φ₂ Y<:T₂) with uniq-⇒ t⇒Φ₁ t⇒Φ₂
... | refl = refl

ext:∈ : ∀ {x y Γ B}
  → (x ≢ y)
  → ¬ ∃[ A ](x ∶ A ∈ Γ)
  → ¬ ∃[ A ](x ∶ A ∈ Γ , y ∶ B)
ext:∈ x≠y ¬x:A∈Γ (A , Z:) = x≠y refl
ext:∈ x≠y ¬x:A∈Γ (A , S: _ x:A∈Γ) = ¬x:A∈Γ (A , x:A∈Γ)

ext:∈<: : ∀ {x Γ S T}
  → ¬ ∃[ A ](x ∶ A ∈ Γ)
  → ¬ ∃[ A ](x ∶ A ∈ Γ , S <: T)
ext:∈<: ¬x:A∈Γ (A , S:-Skip<: x:A∈Γ) = ¬x:A∈Γ (A , x:A∈Γ)

lookup : (Γ : Context) → (x : Id)
  → Dec (∃[ A ](x ∶ A ∈ Γ))
lookup ∅ x = no λ ()
lookup (Γ , y ∶ B) x with x ≟ y
... | yes refl = yes (B , Z:)
... | no x≠y with lookup Γ x
...   | no ¬x:A∈Γ = no (ext:∈ x≠y ¬x:A∈Γ)
...   | yes (A , x:A∈Γ) = yes (A , S: x≠y x:A∈Γ)
lookup (Γ , _ <: _) x with lookup Γ x
... | yes (A , x:A∈Γ) = yes (A , S:-Skip<: x:A∈Γ)
... | no ¬x:A∈Γ = no (ext:∈<: ¬x:A∈Γ)

ext<:∈ : ∀ {X Y Γ U}
  → (X ≢ Y)
  → ¬ ∃[ T ](X <: T ∈ Γ)
  → ¬ ∃[ T ](X <: T ∈ Γ , Y <: U)
ext<:∈ X≠Y ¬X<:T∈Γ (T , Z<:) = X≠Y refl
ext<:∈ X≠Y ¬X<:T∈Γ (T , S<: _ X<:T∈Γ) = ¬X<:T∈Γ (T , X<:T∈Γ)

ext<:∈: : ∀ {Γ X y U}
  → ¬ ∃[ T ](X <: T ∈ Γ)
  → ¬ ∃[ T ](X <: T ∈ Γ , y ∶ U)
ext<:∈: ¬X<:T∈Γ (T , S<:-Skip: X<:T∈Γ) = ¬X<:T∈Γ (T , X<:T∈Γ)

lookup<: : (Γ : Context) → (X : Id)
  → Dec (∃[ T ](X <: T ∈ Γ))
lookup<: ∅ X = no λ ()
lookup<: (Γ , Y <: U) X with X ≟ Y
... | yes refl = yes (U , Z<:)
... | no X≠Y with lookup<: Γ X
...   | no ¬X<:T∈Γ = no (ext<:∈ X≠Y ¬X<:T∈Γ)
...   | yes (T , X<:T∈Γ) = yes (T , S<: X≠Y X<:T∈Γ)
lookup<: (Γ , Y ∶ U) X with lookup<: Γ X
... | yes (T , X<:T∈Γ) = yes (T , S<:-Skip: X<:T∈Γ)
... | no ¬X<:T∈Γ = no (ext<:∈: ¬X<:T∈Γ)

app-arg-wrong-type : ∀ {Γ t₁ t₂ A B}
  → Γ ⊢ t₁ ⇒ A ⇨ B
  → ¬ Γ ⊢ t₂ ⇐ A
  → ¬ ∃[ B' ](Γ ⊢ t₁ ∙ t₂ ⇒ B')
app-arg-wrong-type t₁⇒A⇨B ¬t₂⇐A (B' , BT-App t₁⇒A'⇨B' t₂⇐A') with uniq-⇒ t₁⇒A⇨B t₁⇒A'⇨B'
... | refl = ¬t₂⇐A t₂⇐A'

tapp-arg-wrong-type : ∀ {Γ t X T U Y}
  → Γ ⊢ t ⇒ Φ X <: T ∶ U
  → ¬ Γ ⊢ Y <: T
  → ¬ ∃[ B ](Γ ⊢ t [ Y ] ⇒ B)
tapp-arg-wrong-type t⇒Φ ¬Y<:T (_ , BT-TApp t⇒Φ' Y<:T) with uniq-⇒ t⇒Φ t⇒Φ'
... | refl = ¬Y<:T Y<:T

helper2 : ∀ {Γ A B}
  → A ≡ B
  → ¬ Γ ⊢ A <: B
  → ⊥
helper2 refl ¬A<:B = ¬A<:B S-Refl

helper3 : ∀ {Γ A B T}
  → A ≡ B
  → ¬ Γ ⊢ A <: T
  → Γ ⊢ B <: T
  → ⊥
helper3 refl ¬A<:T B<:T = ¬A<:T B<:T

helper4 : ∀ {Γ A B}
  → A ≡ B
  → ¬ Γ ⊢ A <: B
  → ⊥
helper4 refl ¬A<:B = ¬A<:B S-Refl

inferType :
    (Γ : Context)
  → (t : Term)
  → Dec (∃[ A ](Γ ⊢ t ⇒ A))

checkType :
    (Γ : Context)
  → (t : Term)
  → (A : Type)
  → Dec (Γ ⊢ t ⇐ A)

isSubType :
    (Γ : Context)
  → (S : Type)
  → (T : Type)
  → Dec (Γ ⊢ S <: T)

inferType Γ (′ x) with lookup Γ x
... | yes (A , x:A∈Γ) = yes (A , BT-Var x:A∈Γ)
... | no ¬x∈Γ = no λ{(A , (BT-Var x:A∈Γ)) → ¬x∈Γ (A , x:A∈Γ)}
inferType Γ (t₁ ∙ t₂) with inferType Γ t₁
... | no ¬t₁⇒T = no λ{(B , BT-App t₁⇒A⇨B _) → ¬t₁⇒T (_ , t₁⇒A⇨B)}
... | yes (TTrue , t₁⇒TTrue) = no λ{(B , BT-App t₁⇒A⇨B _) → TTrue≠⇨ (uniq-⇒ t₁⇒TTrue t₁⇒A⇨B)}
... | yes (TFalse , t₁⇒TFalse) = no λ{(B , BT-App t₁⇒A⇨B _) → TFalse≠⇨ (uniq-⇒ t₁⇒TFalse t₁⇒A⇨B)}
... | yes (Top , t₁⇒Top) = no λ{(B , BT-App t₁⇒A⇨B _) → Top≠⇨ (uniq-⇒ t₁⇒Top t₁⇒A⇨B)}
... | yes (′′ x , t₁⇒′′) = no λ{(B , BT-App t₁⇒A⇨B _) → ⇨≠′′ (uniq-⇒ t₁⇒A⇨B t₁⇒′′)}
... | yes (Φ x <: t ∶ t₃ , t₁⇒Φ) = no λ{(B , BT-App t₁⇒A⇨B _) → ⇨≠Φ (uniq-⇒ t₁⇒A⇨B t₁⇒Φ)}
... | yes (A ∨ B , t₁⇒∨) = no λ{(B , BT-App t₁⇒A⇨B _) → ⇨≠∨ (uniq-⇒ t₁⇒A⇨B t₁⇒∨)}
... | yes (A ⇨ B , t₁⇒A⇨B) with checkType Γ t₂ A
...   | no ¬t₂⇐A = no (app-arg-wrong-type t₁⇒A⇨B ¬t₂⇐A)
...   | yes t₂⇐A = yes (B , BT-App t₁⇒A⇨B t₂⇐A)
inferType Γ (t ↓ T) with checkType Γ t T
... | yes t⇐T = yes (T , BT-Ann t⇐T)
... | no ¬t⇐T = no λ{(_ , BT-Ann t⇐T) → ¬t⇐T t⇐T}
inferType Γ (B′ true) = yes (TTrue , BT-True)
inferType Γ (B′ false) = yes (TFalse , BT-False)
inferType Γ (t [ Y ]) with inferType Γ t
... | no ¬t⇒T = no λ{(_ , BT-TApp t⇒A⇨B _) → ¬t⇒T (_ , t⇒A⇨B)}
... | yes (TTrue , t⇒TTrue) = no λ{(_ , BT-TApp t⇒Φ _) → TTrue≠Φ (uniq-⇒ t⇒TTrue t⇒Φ)}
... | yes (TFalse , t⇒TFalse) = no λ{(_ , BT-TApp t⇒Φ _) → TFalse≠Φ (uniq-⇒ t⇒TFalse t⇒Φ)}
... | yes (A ⇨ B , t⇒A⇨B) = no λ{(_ , BT-TApp t⇒Φ _) → ⇨≠Φ (uniq-⇒ t⇒A⇨B t⇒Φ)}
... | yes (Top , t⇒Top) = no λ{(_ , BT-TApp t⇒Φ _) → Top≠Φ (uniq-⇒ t⇒Top t⇒Φ)}
... | yes (′′ x , t⇒′′) = no λ{(_ , BT-TApp t⇒Φ _) → Φ≠′′ (uniq-⇒ t⇒Φ t⇒′′)}
... | yes (A ∨ B , t⇒∨) = no λ{(_ , BT-TApp t⇒Φ _) → Φ≠∨ (uniq-⇒ t⇒Φ t⇒∨)}
... | yes (Φ X <: T ∶ U , t⇒Φ) with isSubType Γ Y T
...   | no ¬Y<:T = no (tapp-arg-wrong-type t⇒Φ ¬Y<:T)
...   | yes Y<:T = yes (U [ X τ= Y ] , BT-TApp t⇒Φ Y<:T)
inferType Γ (if x then x₁ else x₂) = no λ {(_ , ())}
inferType Γ (ƛ x ⋯> x₁) = no λ {(_ , ())}
inferType Γ (Λ x <: x₁ ⋯> x₂) = no λ {(_ , ())}

checkType Γ (if t₁ then t₂ else t₃) T with checkType Γ t₁ TBool | checkType Γ t₂ T | checkType Γ t₃ T
... | no ¬t₁⇐TBool | _ | _ = no λ{(BT-If x _ _) → ¬t₁⇐TBool x ; (BT-CheckInfer () refl); (BT-Sub () _)}
... | _ | no ¬t₂⇐T | _ = no λ{(BT-If _ x _) → ¬t₂⇐T x ; (BT-CheckInfer () refl); (BT-Sub () _)}
... | _ | _ | no ¬t₃⇐T = no λ{(BT-If _ _ x) → ¬t₃⇐T x ; (BT-CheckInfer () refl); (BT-Sub () _)}
... | yes t₁⇐TBool | yes t₂⇐T | yes t₃⇐T = yes (BT-If t₁⇐TBool t₂⇐T t₃⇐T)
checkType Γ (ƛ x ⋯> t) (A ⇨ B) with checkType (Γ , x ∶ A) t B
... | yes t⇐B = yes (BT-Abs t⇐B)
... | no ¬t⇐B = no λ{(BT-Abs t⇐B) → ¬t⇐B t⇐B ; (BT-CheckInfer () refl) ; (BT-Sub () _)}
checkType Γ (ƛ x ⋯> t) TTrue = no λ{(BT-CheckInfer () refl) ; (BT-Sub () _)}
checkType Γ (ƛ x ⋯> t) TFalse = no λ{(BT-CheckInfer () refl) ; (BT-Sub () _)}
checkType Γ (ƛ x ⋯> a) Top = no λ{(BT-CheckInfer () refl) ; (BT-Sub () _)}
checkType Γ (ƛ x ⋯> a) (′′ X) = no λ{(BT-CheckInfer () refl) ; (BT-Sub () _)}
checkType Γ (ƛ x ⋯> a) (Φ X <: T ∶ U) = no λ{(BT-CheckInfer () refl) ; (BT-Sub () _)}
checkType Γ (ƛ x ⋯> t) (A ∨ B) = no λ{(BT-CheckInfer () refl) ; (BT-Sub () _)}
checkType Γ (Λ X <: T ⋯> U) TTrue = no λ{(BT-CheckInfer () refl) ; (BT-Sub () _)}
checkType Γ (Λ X <: T ⋯> U) TFalse = no λ{(BT-CheckInfer () refl) ; (BT-Sub () _)}
checkType Γ (Λ X <: T ⋯> U) (A ⇨ B) = no λ{(BT-CheckInfer () refl) ; (BT-Sub () _)}
checkType Γ (Λ X <: T ⋯> U) Top = no λ{(BT-CheckInfer () refl) ; (BT-Sub () _)}
checkType Γ (Λ X <: T ⋯> U) (′′ Y) = no λ{(BT-CheckInfer () refl) ; (BT-Sub () _)}
checkType Γ (Λ X <: T ⋯> U) (A ∨ B) = no λ{(BT-CheckInfer () refl) ; (BT-Sub () _)}
checkType Γ (Λ X <: T ⋯> t) (Φ X' <: T' ∶ U) with X ≟ X' | T ≟Tp T'
... | no X≠X' | _ = no λ{(BT-TAbs _) → X≠X' refl ; (BT-CheckInfer () _) ; (BT-Sub () _)}
... | _ | no T≠T' = no λ{(BT-TAbs _) → T≠T' refl ; (BT-CheckInfer () _) ; (BT-Sub () _)}
... | yes refl | yes refl with checkType (Γ , X <: T) t U
...   | yes t⇐U = yes (BT-TAbs t⇐U)
...   | no ¬t⇐U = no λ{(BT-TAbs t⇐U) → ¬t⇐U t⇐U ; (BT-CheckInfer () _) ; (BT-Sub () _)}
checkType Γ (′ x) T with inferType Γ (′ x)
... | no ¬t⇒T = no λ{(BT-CheckInfer {A = A} t⇒T refl) → ¬t⇒T (A , t⇒T) ; (BT-Sub {A = A} t⇒T _) → ¬t⇒T (A , t⇒T)}
... | yes (S , t⇒S) with isSubType Γ S T
...   | yes S<:T = yes (BT-Sub t⇒S S<:T)
...   | no ¬S<:T = no λ{(BT-CheckInfer t⇒T refl) → helper2 (uniq-⇒ t⇒S t⇒T) ¬S<:T ; (BT-Sub t⇒A A<:T) → helper3 (uniq-⇒ t⇒S t⇒A) ¬S<:T A<:T}
checkType Γ (t [ A ]) T with inferType Γ (t [ A ])
... | no ¬t⇒T = no λ{(BT-CheckInfer {A = A} t⇒T refl) → ¬t⇒T (A , t⇒T) ; (BT-Sub {A = A} t⇒T _) → ¬t⇒T (A , t⇒T)}
... | yes (S , t⇒S) with isSubType Γ S T
...   | yes S<:T = yes (BT-Sub t⇒S S<:T)
...   | no ¬S<:T = no λ{(BT-CheckInfer t⇒T refl) → helper2 (uniq-⇒ t⇒S t⇒T) ¬S<:T ; (BT-Sub t⇒A A<:T) → helper3 (uniq-⇒ t⇒S t⇒A) ¬S<:T A<:T}
checkType Γ (t ↓ A) T with inferType Γ (t ↓ A)
... | no ¬t⇒T = no λ{(BT-CheckInfer {A = A} t⇒T refl) → ¬t⇒T (A , t⇒T) ; (BT-Sub {A = A} t⇒T _) → ¬t⇒T (A , t⇒T)}
... | yes (S , t⇒S) with isSubType Γ S T
...   | yes S<:T = yes (BT-Sub t⇒S S<:T)
...   | no ¬S<:T = no λ{(BT-CheckInfer t⇒T refl) → helper2 (uniq-⇒ t⇒S t⇒T) ¬S<:T ; (BT-Sub t⇒A A<:T) → helper3 (uniq-⇒ t⇒S t⇒A) ¬S<:T A<:T}
checkType Γ (B′ b) T with inferType Γ (B′ b)
... | no ¬t⇒T = no λ{(BT-CheckInfer {A = A} t⇒T refl) → ¬t⇒T (A , t⇒T) ; (BT-Sub {A = A} t⇒T _) → ¬t⇒T (A , t⇒T)}
... | yes (S , t⇒S) with isSubType Γ S T
...   | yes S<:T = yes (BT-Sub t⇒S S<:T)
...   | no ¬S<:T = no λ{(BT-CheckInfer t⇒T refl) → helper2 (uniq-⇒ t⇒S t⇒T) ¬S<:T ; (BT-Sub t⇒A A<:T) → helper3 (uniq-⇒ t⇒S t⇒A) ¬S<:T A<:T}
checkType Γ (t₁ ∙ t₂) T with inferType Γ (t₁ ∙ t₂)
... | no ¬t⇒T = no λ{(BT-CheckInfer {A = A} t⇒T refl) → ¬t⇒T (A , t⇒T) ; (BT-Sub {A = A} t⇒T _) → ¬t⇒T (A , t⇒T)}
... | yes (S , t⇒S) with isSubType Γ S T
...   | yes S<:T = yes (BT-Sub t⇒S S<:T)
...   | no ¬S<:T = no λ{(BT-CheckInfer t⇒T refl) → helper2 (uniq-⇒ t⇒S t⇒T) ¬S<:T ; (BT-Sub t⇒A A<:T) → helper3 (uniq-⇒ t⇒S t⇒A) ¬S<:T A<:T}

helper-⇨ : ∀ {Γ S₁ S₂ T₁ T₂}
  → Γ ⊢ S₁ ⇨ S₂ <: T₁ ⇨ T₂
  → Γ ⊢ T₁ <: S₁ × Γ ⊢ S₂ <: T₂
helper-⇨ S-Refl = (S-Refl , S-Refl)
helper-⇨ (S-Arrow x y) = (x , y)
helper-⇨ (S-Trans x y) with inversion-<:-abs y
... | inj₁ (_ , refl) = ⊥-elim (imp-⇨<:′′ x)
... | inj₂ (U₁ , U₂ , T₁<:U₁ , U₂<:T₂ , refl) with helper-⇨ x
...   | (U₁<:S₁ , S₂<:U₂) = (S-Trans T₁<:U₁ U₁<:S₁ , S-Trans S₂<:U₂ U₂<:T₂)

imp-trans-⇨ : ∀ {Γ T₁ T₂ S₁ S₂ U}
  → Γ ⊢ U <: T₁ ⇨ T₂
  → Γ ⊢ S₁ ⇨ S₂ <: U
  → ¬ Γ ⊢ T₁ <: S₁
  → ⊥
imp-trans-⇨ U<:⇨ ⇨<:U ¬T₁<:S₁ with inversion-<:-abs U<:⇨
... | inj₁ (_ , refl) = imp-⇨<:′′ ⇨<:U
... | inj₂ (_ , _ , T₁<:U₁ , _ , refl) with helper-⇨ ⇨<:U
...   | (U₁<:S₁ , _) = ¬T₁<:S₁ (S-Trans T₁<:U₁ U₁<:S₁)

imp-trans2-⇨ : ∀ {Γ T₁ T₂ S₁ S₂ U}
  → Γ ⊢ U <: T₁ ⇨ T₂
  → Γ ⊢ S₁ ⇨ S₂ <: U
  → ¬ Γ ⊢ S₂ <: T₂
  → ⊥
imp-trans2-⇨ U<:⇨ ⇨<:U ¬S₂<:T₂ with inversion-<:-abs U<:⇨
... | inj₁ (_ , refl) = imp-⇨<:′′ ⇨<:U
... | inj₂ (_ , _ , _ , U₂<:T₂ , refl) with helper-⇨ ⇨<:U
...   | (_ , S₂<:U₂) = ¬S₂<:T₂ (S-Trans S₂<:U₂ U₂<:T₂)

helper-Φ : ∀ {Γ X₁ X₂ U₁ U₂ S T}
  → Γ ⊢ Φ X₁ <: U₁ ∶ S <: Φ X₂ <: U₂ ∶ T
  → X₁ ≡ X₂ × U₁ ≡ U₂ × Γ , X₁ <: U₁ ⊢ S <: T
helper-Φ S-Refl = (refl , refl , S-Refl)
helper-Φ (S-All x) = (refl , refl , x)
helper-Φ (S-Trans x y) with inversion-<:-forall y
... | inj₁ (_ , refl) = ⊥-elim (imp-Φ<:′′ x)
... | inj₂ (_ , z , refl) with helper-Φ x
...   | (refl , refl , c) = (refl , refl , S-Trans c z)

imp-trans-Φ : ∀ {Γ X₁ X₂ U₁ U₂ S T U}
  → Γ ⊢ U <: (Φ X₁ <: U₁ ∶ S)
  → Γ ⊢ (Φ X₂ <: U₂ ∶ T) <: U
  → ¬ X₂ ≡ X₁
  → ⊥
imp-trans-Φ U<:Φ Φ<:U ¬X₁≠X₂ with inversion-<:-forall U<:Φ
... | inj₁ (_ , refl) = imp-Φ<:′′ Φ<:U
... | inj₂ (_ , _ , refl) with helper-Φ Φ<:U
...   | (refl , refl , _) = ¬X₁≠X₂ refl

imp-trans2-Φ : ∀ {Γ X₁ X₂ U₁ U₂ S T U}
  → Γ ⊢ U <: (Φ X₁ <: U₁ ∶ S)
  → Γ ⊢ (Φ X₂ <: U₂ ∶ T) <: U
  → ¬ U₂ ≡ U₁
  → ⊥
imp-trans2-Φ U<:Φ Φ<:U ¬U₁≠U₂ with inversion-<:-forall U<:Φ
... | inj₁ (_ , refl) = imp-Φ<:′′ Φ<:U
... | inj₂ (_ , _ , refl) with helper-Φ Φ<:U
...   | (refl , refl , _) = ¬U₁≠U₂ refl

imp-trans3-Φ : ∀ {Γ X₁ X₂ U₁ U₂ S T U}
  → Γ ⊢ U <: (Φ X₁ <: U₁ ∶ S)
  → Γ ⊢ (Φ X₂ <: U₂ ∶ T) <: U
  → ¬ (Γ , X₂ <: U₂) ⊢ T <: S
  → ⊥
imp-trans3-Φ U<:Φ Φ<:U ¬T<:S with inversion-<:-forall U<:Φ
... | inj₁ (_ , refl) = imp-Φ<:′′ Φ<:U
... | inj₂ (_ , U<:S , refl) with helper-Φ Φ<:U
...   | (refl , refl , T<:U) = ¬T<:S (S-Trans T<:U U<:S)

{-# TERMINATING #-}
isSubType Γ TTrue TTrue = yes S-Refl
isSubType Γ TTrue TFalse = no imp-TTrue<:TFalse
isSubType Γ TTrue (A ⇨ B) = no imp-TTrue<:⇨
isSubType Γ TTrue Top = yes S-Top
isSubType Γ TTrue (′′ X) = no imp-TTrue<:′′
isSubType Γ TTrue (Φ x <: T ∶ T₁) = no imp-TTrue<:Φ
isSubType Γ TTrue (A ∨ B) with isSubType Γ TTrue A | isSubType Γ TTrue B
... | yes True<:A | _ = yes (S-Trans True<:A (S-UnionL S-Refl))
... | _ | yes True<:B = yes (S-Trans True<:B (S-UnionR S-Refl))
... | no ¬True<:A | no ¬True<:B = no λ{x → imp-TTrue<:∨ x ¬True<:A ¬True<:B}
isSubType Γ TFalse TFalse = yes S-Refl
isSubType Γ TFalse TTrue = no imp-TFalse<:TTrue
isSubType Γ TFalse (A ⇨ B) = no imp-TFalse<:⇨
isSubType Γ TFalse Top = yes S-Top
isSubType Γ TFalse (′′ X) = no imp-TFalse<:′′
isSubType Γ TFalse (Φ x <: T ∶ T₁) = no imp-TFalse<:Φ
isSubType Γ TFalse (A ∨ B) with isSubType Γ TFalse A | isSubType Γ TFalse B
... | yes False<:A | _ = yes (S-Trans False<:A (S-UnionL S-Refl))
... | _ | yes False<:B = yes (S-Trans False<:B (S-UnionR S-Refl))
... | no ¬False<:A | no ¬False<:B = no λ{x → imp-TFalse<:∨ x ¬False<:A ¬False<:B}
isSubType Γ (A ⇨ B) TTrue = no imp-⇨<:TTrue
isSubType Γ (A ⇨ B) TFalse = no imp-⇨<:TFalse
isSubType Γ (A ⇨ B) Top = yes S-Top
isSubType Γ (A ⇨ B) (′′ x) = no imp-⇨<:′′
isSubType Γ (A ⇨ B) (Φ x <: T ∶ T₁) = no imp-⇨<:Φ
isSubType Γ (S₁ ⇨ S₂) (T₁ ⇨ T₂) with isSubType Γ T₁ S₁ | isSubType Γ S₂ T₂
... | yes T₁<:S₁ | yes S₂<:T₂ = yes (S-Arrow T₁<:S₁ S₂<:T₂)
... | no ¬T₁<:S₁ | _ = no λ{S-Refl → ¬T₁<:S₁ S-Refl ; (S-Trans x y) → imp-trans-⇨ y x ¬T₁<:S₁ ; (S-Arrow T₁<:S₁ _) → ¬T₁<:S₁ T₁<:S₁}
... | _ | no ¬S₂<:T₂ = no λ{S-Refl → ¬S₂<:T₂ S-Refl ; (S-Trans x y) → imp-trans2-⇨ y x ¬S₂<:T₂ ; (S-Arrow _ S₂<:T₂) → ¬S₂<:T₂ S₂<:T₂}
isSubType Γ (A ⇨ B) (L ∨ R) with isSubType Γ (A ⇨ B) L | isSubType Γ (A ⇨ B) R
... | yes ⇨<:L | _ = yes (S-Trans ⇨<:L (S-UnionL S-Refl))
... | _ | yes ⇨<:R = yes (S-Trans ⇨<:R (S-UnionR S-Refl))
... | no ¬⇨<:L | no ¬⇨<:R = no λ{x → imp-⇨<:∨ x ¬⇨<:L ¬⇨<:R}
isSubType Γ Top TTrue = no imp-Top<:TTrue
isSubType Γ Top TFalse = no imp-Top<:TFalse
isSubType Γ Top (A ⇨ B) = no imp-Top<:⇨
isSubType Γ Top Top = yes S-Refl
isSubType Γ Top (′′ x) = no imp-Top<:′′
isSubType Γ Top (Φ x <: T ∶ T₁) = no imp-Top<:Φ
isSubType Γ Top (L ∨ R) with isSubType Γ Top L | isSubType Γ Top R
... | yes Top<:L | _ = yes (S-Trans Top<:L (S-UnionL S-Refl))
... | _ | yes Top<:R = yes (S-Trans Top<:R (S-UnionR S-Refl))
... | no ¬Top<:L | no ¬Top<:R = no λ{x → imp-Top<:∨ x ¬Top<:L ¬Top<:R}
isSubType Γ (′′ X) T with T ≟Tp Top | T ≟Tp ′′ X
... | yes refl | _ = yes S-Top
... | _ | yes refl = yes S-Refl
... | no T≠Top | no T≠X with lookup<: Γ X
...   | no ¬X<:S∈Γ = {!!}
-- no λ{S-Refl → T≠X refl ; (S-Trans x y) → {!!} ; S-Top → T≠Top refl ; (S-TVar X<:T∈Γ) → ¬X<:S∈Γ (T , X<:T∈Γ)}
...   | yes (S , X<:S∈Γ) with S ≟Tp ′′ X
--      TODO: X <: ′′ X and other cycles* should be made impossible and thus lead to a contradiction
--      * such as X <: ′′ Y ∈ Γ ∧ Y <: ′′ X ∈ Γ
...     | yes refl = no λ{c → {!!}}
...     | no S≠X with isSubType Γ S T
...       | yes S<:T = yes (S-Trans (S-TVar X<:S∈Γ) S<:T)
...       | no ¬S<:T = {!!}
-- no λ{S-Refl → T≠X refl ; (S-Trans x y) → {!!} ; S-Top → T≠Top refl ; (S-TVar X<:T∈Γ) → helper4 (uniq-<:∈ X<:S∈Γ X<:T∈Γ) ¬S<:T}
isSubType Γ (Φ X <: T ∶ U) TTrue = no imp-Φ<:TTrue
isSubType Γ (Φ X <: T ∶ U) TFalse = no imp-Φ<:TFalse
isSubType Γ (Φ X <: T ∶ U) (A ⇨ B) = no imp-Φ<:⇨
isSubType Γ (Φ X <: T ∶ U) Top = yes S-Top
isSubType Γ (Φ X <: T ∶ U) (′′ Y) = no imp-Φ<:′′
isSubType Γ (Φ X₁ <: U₁ ∶ S) (Φ X₂ <: U₂ ∶ T) with X₁ ≟ X₂ | U₁ ≟Tp U₂ | isSubType (Γ , X₁ <: U₁) S T
... | yes refl | yes refl | yes S<:T = yes (S-All S<:T)
... | no X₁≠X₂ | _ | _ = no λ{S-Refl → X₁≠X₂ refl ; (S-Trans x y) → imp-trans-Φ y x X₁≠X₂ ; (S-All _) → X₁≠X₂ refl}
... | _ | no U₁≠U₂ | _ = no λ{S-Refl → U₁≠U₂ refl ; (S-Trans x y) → imp-trans2-Φ y x U₁≠U₂ ; (S-All _) → U₁≠U₂ refl}
... | _ | _ | no ¬S<:T = no λ{S-Refl → ¬S<:T S-Refl ; (S-Trans x y) → imp-trans3-Φ y x ¬S<:T ; (S-All S<:T) → ¬S<:T S<:T}
isSubType Γ (Φ X <: T ∶ U) (L ∨ R) with isSubType Γ (Φ X <: T ∶ U) L | isSubType Γ (Φ X <: T ∶ U) R
... | yes Φ<:L | _ = yes (S-Trans Φ<:L (S-UnionL S-Refl))
... | _ | yes Φ<:R = yes (S-Trans Φ<:R (S-UnionR S-Refl))
... | no ¬Φ<:L | no ¬Φ<:R = no λ{x → imp-Φ<:∨ x ¬Φ<:L ¬Φ<:R}
isSubType Γ (A ∨ B) TTrue = no imp-∨<:TTrue
isSubType Γ (A ∨ B) TFalse = no imp-∨<:TFalse
isSubType Γ (A ∨ B) (_ ⇨ _) = no imp-∨<:⇨
isSubType Γ (A ∨ B) Top = yes S-Top
isSubType Γ (A ∨ B) (′′ _) = no imp-∨<:′′
isSubType Γ (A ∨ B) (Φ _ <: _ ∶ _) = no imp-∨<:Φ
isSubType Γ (A₁ ∨ B₁) (A₂ ∨ B₂) with isSubType Γ (A₁ ∨ B₁) A₂ | isSubType Γ (A₁ ∨ B₁) B₂
... | yes ∨<:A₂ | _ = {!!}
... | _ | yes ∨<:B₂ = {!!}
... | no ¬∨<:A₂ | no ¬∨<:B₂ = {!!}

test1 = isSubType ∅ TBool TBool

test2 = (ƛ "x" ⋯> if (′"x") then (′"x") else (′"x")) ↓ (′′ "X" ⇨ ′′ "X")

test3 = ((Λ "X" <: TBool ⋯> test2) ↓ (Φ "X" <: TBool ∶ (′′ "X" ⇨ ′′ "X"))) [ TTrue ]
test3a = checkType ∅ test3 (TTrue ⇨ TTrue)

test5 = (ƛ "x" ⋯> if (′"x") then (′"x") else (′"x")) ↓ (TBool ⇨ TBool)
test5a = checkType ∅ test5 (TBool ⇨ TBool)
test5b = checkType ∅ test5 (TTrue ⇨ TBool)
test5c = ′"x"
test5d = checkType (∅ , "x" ∶ TBool) test5c TBool

test6 = (ƛ "x" ⋯> if (′"x") then (′"x") else (′"x")) ↓ (TTrue ⇨ TTrue)
test6a = checkType ∅ test6 (TTrue ⇨ TTrue)
test6b = checkType ∅ test6 (TTrue ⇨ TBool)

{-
symbols:
≟ = \?=
⊎ = \u+
₁ = \_1
₂ = \_2
′ = \'
→ = \r1 (or \rightarrow)
ƛ = \Gl-
∶ = \:
⇒ = \=> (or \r2)
∙ = \.
⋯ = \...
⋯> = \... >
∅ = \emptyset
⊢ = \|-
Γ = \GG
Δ = \GD
⊥ = \bot
— = \em
≢ = \==n
⊤ = \top
⇐ = \l2
⇨ = \r7
⁺ = \^+
⁻ = \^-
↓ = \d1
↑ = \u1
¬ = \neg
-}
