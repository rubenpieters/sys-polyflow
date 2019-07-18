module Bidir where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym)
open import Data.String using (String; _≟_)
open import Data.Bool using (Bool; true; false)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (∃; ∃-syntax; _,_; _×_)
open import Data.Unit using (⊤; tt)

Id : Set
Id = String

-- -------------------------------------
-- TYPES

infix 50 _⇨_

data Type : Set where
  TBool : Type
  _⇨_ : Type → Type → Type

-- -------------------------------------

-- -------------------------------------
-- TERMS

infix 50 ′_
infix 50 B′_
infixl 45 _↓_
infix 45 _↑
infixl 40 _∙_
infix 35 if_then_else
infix 30 ƛ_⋯>_

data Term⁺ : Set
data Term⁻ : Set

data Term⁺ where
  -- variables
  ′_ : Id → Term⁺
  -- application
  _∙_ : Term⁺ → Term⁻ → Term⁺
  -- annotation
  _↓_ : Term⁻ → Type → Term⁺
  -- bool literals
  B′_ : Bool → Term⁺

data Term⁻ where
  -- if expr
  if_then_else : Term⁺ → Term⁻ → Term⁻ → Term⁻
  -- function abstraction
  ƛ_⋯>_ : Id → Term⁻ → Term⁻
  -- lift
  _↑ : Term⁺ → Term⁻

-- -------------------------------------

-- -------------------------------------
-- CONTEXT

-- definition

infixl 50 _,_∶_

data Context : Set where
  ∅ : Context
  _,_∶_ : Context → Id → Type → Context

-- has-type-in-context relation

data _∶_∈_ : Id → Type → Context → Set where
  Z : ∀ {x T Γ}
    → x ∶ T ∈ Γ , x ∶ T
  S : ∀ {x T Γ y U}
    → x ≢ y
    → x ∶ T ∈ Γ
    → x ∶ T ∈ Γ , y ∶ U

-- -------------------------------------

-- -------------------------------------
-- TYPING

data _⊢_⇒_ : Context → Term⁺ → Type → Set
data _⊢_⇐_ : Context → Term⁻ → Type → Set

data _⊢_⇒_ where
  BT-Var : ∀ {Γ x A}
    → x ∶ A ∈ Γ
    → Γ ⊢ ′ x ⇒ A
  BT-True : ∀ {Γ}
    → Γ ⊢ B′ true ⇒ TBool
  BT-False : ∀ {Γ}
    → Γ ⊢ B′ false ⇒ TBool
  BT-App : ∀ {Γ t₁ t₂ A B}
    → Γ ⊢ t₁ ⇒ A ⇨ B
    → Γ ⊢ t₂ ⇐ A
    → Γ ⊢ t₁ ∙ t₂ ⇒ B
  BT-Ann : ∀ {Γ t T}
    → Γ ⊢ t ⇐ T
    → Γ ⊢ t ↓ T ⇒ T

data _⊢_⇐_ where
  BT-If : ∀ {Γ t₁ t₂ t₃ T}
    → Γ ⊢ t₁ ⇒ TBool
    → Γ ⊢ t₂ ⇐ T
    → Γ ⊢ t₃ ⇐ T
    → Γ ⊢ if t₁ then t₂ else t₃ ⇐ T
  BT-Abs : ∀ {Γ x t A B}
    → Γ , x ∶ A ⊢ t ⇐ B
    → Γ ⊢ (ƛ x ⋯> t) ⇐ (A ⇨ B)
  BT-CheckInfer : ∀ {Γ t A B}
    → Γ ⊢ t ⇒ A
    → A ≡ B
    → Γ ⊢ t ↑ ⇐ B

-- -------------------------------------

_≟Tp_ : (A : Type) → (B : Type) → Dec (A ≡ B)
TBool ≟Tp TBool = yes refl
TBool ≟Tp (b ⇨ b₁) = no λ()
(A ⇨ B) ≟Tp TBool = no λ()
(A₁ ⇨ B₁) ≟Tp (A₂ ⇨ B₂) with A₁ ≟Tp A₂ | B₁ ≟Tp B₂
... | no A₁≢A₂ | _ = no  λ{refl → A₁≢A₂ refl}
... | yes _    | no B₁≢B₂ = no λ{refl → B₁≢B₂ refl}
... | yes refl | yes refl = yes refl

ext∈ : ∀ {x y Γ B}
  → (x ≢ y)
  → ¬ ∃[ A ](x ∶ A ∈ Γ)
  → ¬ ∃[ A ](x ∶ A ∈ Γ , y ∶ B)
ext∈ x≠y ¬∃ (A , Z) = x≠y refl
ext∈ x≠y ¬∃ (A , S _ x:A∈Γ) = ¬∃ (A , x:A∈Γ)

lookup : (Γ : Context) → (x : Id)
  → Dec (∃[ A ](x ∶ A ∈ Γ))
lookup ∅ x = no (λ ())
lookup (Γ , y ∶ B) x with x ≟ y
... | yes refl = yes (B , Z)
... | no x≠y with lookup Γ x
...   | no ¬∃ = no (ext∈ x≠y ¬∃)
...   | yes (A , x:A∈Γ) = yes (A , S x≠y x:A∈Γ)

inferType :
    (Γ : Context)
  → (t : Term⁺)
  → Dec (∃[ A ](Γ ⊢ t ⇒ A))

checkType :
    (Γ : Context)
  → (t : Term⁻)
  → (A : Type)
  → Dec (Γ ⊢ t ⇐ A)

inferType Γ (′ x) with lookup Γ x
... | yes (A , x:A∈Γ) = yes (A , BT-Var x:A∈Γ)
... | no ¬∃ = no λ{(A , (BT-Var x:A∈Γ)) → ¬∃ (A , x:A∈Γ)}
inferType Γ (t₁ ∙ t₂) with inferType Γ t₁
... | no ¬t₁⇒A = no {!!}
... | yes (TBool , t₁⇒TBool) = no {!!}
... | yes (A ⇨ B , t₁⇒A⇨B) with checkType Γ t₂ A
...   | no ¬t₂⇐A = no {!!}
...   | yes t₂⇐A = yes (B , BT-App t₁⇒A⇨B t₂⇐A)
inferType Γ (t ↓ T) with checkType Γ t T
... | yes t⇐T = yes (T , BT-Ann t⇐T)
... | no ¬t⇐T = no λ{(_ , BT-Ann t⇐T) → ¬t⇐T t⇐T}
inferType Γ (B′ true) = yes (TBool , BT-True)
inferType Γ (B′ false) = yes (TBool , BT-False)

checkType Γ (if t₁ then t₂ else t₃) T with inferType Γ t₁
... | no x = {!!}
... | yes (A ⇨ B , t₁⇒A⇨B) = {!!}
... | yes (TBool , t₁⇒TBool) with checkType Γ t₂ T | checkType Γ t₃ T
...   | yes t₂⇐T | yes t₃⇐T = yes (BT-If t₁⇒TBool t₂⇐T t₃⇐T)
...   | no _ | no _ = {!!}
...   | yes _ | no _ = {!!}
...   | no _ | yes _ = {!!}
checkType Γ (ƛ x ⋯> t) (A ⇨ B) with checkType (Γ , x ∶ A) t B
... | yes t⇐B = yes (BT-Abs t⇐B)
... | no ¬t⇐B = no λ{(BT-Abs t⇐B) → ¬t⇐B t⇐B}
checkType Γ (ƛ x ⋯> t) TBool = no λ()
checkType Γ (t ↑) A with inferType Γ t
... | no z = {!!}
... | yes (B , t⇒B) with A ≟Tp B
...   | yes refl = yes (BT-CheckInfer t⇒B refl)
...   | no A≢B = no {!!}

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
