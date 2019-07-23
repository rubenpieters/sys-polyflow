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

infix 50 _⇨_
infix 50 ′′_
infix 40 Φ_<:_∶_

data Type : Set where
  TBool : Type
  _⇨_ : Type → Type → Type
  Top : Type
  ′′_ : Id → Type
  Φ_<:_∶_ : Id → Type → Type → Type

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

-- inversion

inversion-<:-var : ∀ {Γ S X}
  → Γ ⊢ S <: ′′ X
  → ∃[ Y ](S ≡ ′′ Y)
inversion-<:-var {X = X} (S-Refl) = (X , refl)
inversion-<:-var (S-Trans S<:U U<:′′X) with inversion-<:-var U<:′′X
... | (_ , refl) = inversion-<:-var S<:U
inversion-<:-var (S-TVar {X = X} _) = (X , refl)

inversion-<:-bool : ∀ {Γ S}
  → Γ ⊢ S <: TBool
  → ∃[ X ](S ≡ ′′ X) ⊎ S ≡ TBool
inversion-<:-bool (S-Refl) = inj₂ refl
inversion-<:-bool (S-Trans S<:U U<:TBool) with inversion-<:-bool U<:TBool
... | inj₁ (_ , refl) = inj₁ (inversion-<:-var S<:U)
... | inj₂ refl = inversion-<:-bool S<:U
inversion-<:-bool (S-TVar {X = X} _) = inj₁ (X , refl)

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

-- imp subtyping

imp-TBool<:⇨ : ∀ {Γ A B}
  → Γ ⊢ TBool <: A ⇨ B
  → ⊥
imp-TBool<:⇨ (S-Trans x y) with inversion-<:-abs y
... | inj₂ (a , b , c , d , refl) = imp-TBool<:⇨ x
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()

imp-TBool<:′′ : ∀ {Γ X}
  → Γ ⊢ TBool <: ′′ X
  → ⊥
imp-TBool<:′′ (S-Trans x y) with inversion-<:-var y
... | (_ , refl) = imp-TBool<:′′ x

imp-TBool<:Φ : ∀ {Γ X T U}
  → Γ ⊢ TBool <: Φ X <: T ∶ U
  → ⊥
imp-TBool<:Φ (S-Trans x y) with inversion-<:-forall y
... | inj₂ (a , b , refl) = imp-TBool<:Φ x
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()

imp-⇨<:TBool : ∀ {Γ A B}
  → Γ ⊢ A ⇨ B <: TBool
  → ⊥
imp-⇨<:TBool (S-Trans x y) with inversion-<:-bool y
... | inj₂ refl = imp-⇨<:TBool x
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

imp-Top<:TBool : ∀ {Γ}
  → Γ ⊢ Top <: TBool
  → ⊥
imp-Top<:TBool (S-Trans x y) with inversion-<:-bool y
... | inj₂ refl = imp-Top<:TBool x
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

imp-Φ<:TBool : ∀ {Γ X T U}
  → Γ ⊢ Φ X <: T ∶ U <: TBool
  → ⊥
imp-Φ<:TBool (S-Trans x y) with inversion-<:-bool y
... | inj₂ refl = imp-Φ<:TBool x
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

-- -------------------------------------

-- -------------------------------------
-- TYPING

-- type substitution

infix 50 _[_τ=_]

_[_τ=_] : Type → Id → Type → Type
(′′ x) [ y τ= s ] with x ≟ y
... | yes _ = s
... | no _ = ′′ x
TBool [ y τ= s ] = TBool
(A ⇨ B) [ y τ= s ] = (A [ y τ= s ]) ⇨ (B [ y τ= s ])
(Φ X <: T ∶ U) [ y τ= s ] = Φ X <: (T [ y τ= s ]) ∶ U [ y τ= s ]
Top [ y τ= s ] = Top


data _⊢_⇒_ : Context → Term → Type → Set
data _⊢_⇐_ : Context → Term → Type → Set

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
  BT-TApp : ∀ {Γ t₁ X T U Y}
    → Γ ⊢ t₁ ⇒ (Φ X <: T ∶ U)
    → Γ ⊢ Y <: T
    → Γ ⊢ t₁ [ Y ] ⇒ U [ X τ= Y ]
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
TBool ≟Tp TBool = yes refl
TBool ≟Tp (A ⇨ B) = no λ()
TBool ≟Tp Top = no λ()
TBool ≟Tp (′′ x) = no λ()
TBool ≟Tp (Φ x <: t ∶ t₁) = no λ()
(A ⇨ B) ≟Tp TBool = no λ()
(A ⇨ B) ≟Tp Top = no λ()
(A ⇨ B) ≟Tp (′′ X) = no λ()
(A ⇨ B) ≟Tp (Φ X <: T ∶ U) = no λ()
(A₁ ⇨ B₁) ≟Tp (A₂ ⇨ B₂) with A₁ ≟Tp A₂ | B₁ ≟Tp B₂
... | no A₁≢A₂ | _ = no  λ{refl → A₁≢A₂ refl}
... | yes _    | no B₁≢B₂ = no λ{refl → B₁≢B₂ refl}
... | yes refl | yes refl = yes refl
Top ≟Tp Top = yes refl
Top ≟Tp TBool = no λ()
Top ≟Tp (A ⇨ B) = no λ()
Top ≟Tp (′′ X) = no λ()
Top ≟Tp (Φ X <: T ∶ U) = no λ()
(′′ X₁) ≟Tp (′′ X₂) with X₁ ≟ X₂
... | yes refl = yes refl
... | no X₁≠X₂ = no (λ{refl → X₁≠X₂ refl})
(′′ X) ≟Tp TBool = no λ()
(′′ X) ≟Tp (A ⇨ B) = no λ()
(′′ X) ≟Tp Top = no λ()
(′′ X) ≟Tp (Φ Y <: T ∶ U) = no λ()
(Φ X <: T ∶ U) ≟Tp TBool = no λ()
(Φ X <: T ∶ U) ≟Tp (A ⇨ B) = no λ()
(Φ X <: T ∶ U) ≟Tp Top = no λ()
(Φ X <: T ∶ U) ≟Tp (′′ _) = no λ()
(Φ X₁ <: T₁ ∶ U₁) ≟Tp (Φ X₂ <: T₂ ∶ U₂) with X₁ ≟ X₂ | T₁ ≟Tp T₂ | U₁ ≟Tp U₂
... | no X₁≠X₂ | _ | _ = no λ{refl → X₁≠X₂ refl}
... | yes _ | no T₁≠T₂ | _ = no λ{refl → T₁≠T₂ refl}
... | yes _ | yes _ | no U₁≠U₂ = no λ{refl → U₁≠U₂ refl}
... | yes refl | yes refl | yes refl = yes refl

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

Φ≠′′ : ∀ {X T U Y}
  → Φ X <: T ∶ U ≢ ′′ Y
Φ≠′′ ()

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
... | yes (TBool , t₁⇒TBool) = no λ{(B , BT-App t₁⇒A⇨B _) → TBool≠⇨ (uniq-⇒ t₁⇒TBool t₁⇒A⇨B)}
... | yes (Top , t₁⇒Top) = no λ{(B , BT-App t₁⇒A⇨B _) → Top≠⇨ (uniq-⇒ t₁⇒Top t₁⇒A⇨B)}
... | yes (′′ x , t₁⇒′′) = no λ{(B , BT-App t₁⇒A⇨B _) → ⇨≠′′ (uniq-⇒ t₁⇒A⇨B t₁⇒′′)}
... | yes (Φ x <: t ∶ t₃ , t₁⇒Φ) = no λ{(B , BT-App t₁⇒A⇨B _) → ⇨≠Φ (uniq-⇒ t₁⇒A⇨B t₁⇒Φ)}
... | yes (A ⇨ B , t₁⇒A⇨B) with checkType Γ t₂ A
...   | no ¬t₂⇐A = no (app-arg-wrong-type t₁⇒A⇨B ¬t₂⇐A)
...   | yes t₂⇐A = yes (B , BT-App t₁⇒A⇨B t₂⇐A)
inferType Γ (t ↓ T) with checkType Γ t T
... | yes t⇐T = yes (T , BT-Ann t⇐T)
... | no ¬t⇐T = no λ{(_ , BT-Ann t⇐T) → ¬t⇐T t⇐T}
inferType Γ (B′ true) = yes (TBool , BT-True)
inferType Γ (B′ false) = yes (TBool , BT-False)
inferType Γ (t [ Y ]) with inferType Γ t
... | no ¬t⇒T = no λ{(_ , BT-TApp t⇒A⇨B _) → ¬t⇒T (_ , t⇒A⇨B)}
... | yes (TBool , t⇒TBool) = no λ{(_ , BT-TApp t⇒Φ _) → TBool≠Φ (uniq-⇒ t⇒TBool t⇒Φ)}
... | yes (A ⇨ B , t⇒A⇨B) = no λ{(_ , BT-TApp t⇒Φ _) → ⇨≠Φ (uniq-⇒ t⇒A⇨B t⇒Φ)}
... | yes (Top , t⇒Top) = no λ{(_ , BT-TApp t⇒Φ _) → Top≠Φ (uniq-⇒ t⇒Top t⇒Φ)}
... | yes (′′ x , t⇒′′) = no λ{(_ , BT-TApp t⇒Φ _) → Φ≠′′ (uniq-⇒ t⇒Φ t⇒′′)}
... | yes (Φ X <: T ∶ U , t⇒Φ) with isSubType Γ Y T
...   | no ¬Y<:T = no (tapp-arg-wrong-type t⇒Φ ¬Y<:T)
...   | yes Y<:T = yes (U [ X τ= Y ] , BT-TApp t⇒Φ Y<:T)
inferType Γ (if x then x₁ else x₂) = no λ {(_ , ())}
inferType Γ (ƛ x ⋯> x₁) = no λ {(_ , ())}
inferType Γ (Λ x <: x₁ ⋯> x₂) = no λ {(_ , ())}

checkType Γ (if t₁ then t₂ else t₃) T with inferType Γ t₁
... | no ¬t₁⇒T = no λ{(BT-If t₁⇒TBool _ _) → ¬t₁⇒T (TBool , t₁⇒TBool) ; (BT-CheckInfer () refl) ; (BT-Sub () _)}
... | yes (A ⇨ B , t₁⇒A⇨B) = no λ{(BT-If t₁⇒TBool _ _) → TBool≠⇨ (uniq-⇒ t₁⇒TBool t₁⇒A⇨B) ; (BT-CheckInfer () _) ; (BT-Sub () _)}
... | yes (Top , t₁⇒Top) = no λ{(BT-If t₁⇒TBool _ _) →  TBool≠Top (uniq-⇒ t₁⇒TBool t₁⇒Top) ; (BT-CheckInfer () _) ; (BT-Sub () _)}
... | yes (′′ x , t₁⇒′′) =  no λ{(BT-If t₁⇒TBool _ _) →  TBool≠′′ (uniq-⇒ t₁⇒TBool t₁⇒′′) ; (BT-CheckInfer () _) ; (BT-Sub () _)}
... | yes (Φ x <: x₁ ∶ x₂ , t₁⇒Φ) =  no λ{(BT-If t₁⇒TBool _ _) →  TBool≠Φ (uniq-⇒ t₁⇒TBool t₁⇒Φ) ; (BT-CheckInfer () _) ; (BT-Sub () _)}
... | yes (TBool , t₁⇒TBool) with checkType Γ t₂ T | checkType Γ t₃ T
...   | yes t₂⇐T | yes t₃⇐T = yes (BT-If t₁⇒TBool t₂⇐T t₃⇐T)
...   | no ¬t₂⇐T | _ = no λ{(BT-If _ t₂⇐T _) → ¬t₂⇐T t₂⇐T ; (BT-CheckInfer () _) ; (BT-Sub () _)}
...   | yes _ | no ¬t₃⇐T = no λ{(BT-If _ _ t₃⇐T) → ¬t₃⇐T t₃⇐T ; (BT-CheckInfer () _) ; (BT-Sub () _)}
checkType Γ (ƛ x ⋯> t) (A ⇨ B) with checkType (Γ , x ∶ A) t B
... | yes t⇐B = yes (BT-Abs t⇐B)
... | no ¬t⇐B = no λ{(BT-Abs t⇐B) → ¬t⇐B t⇐B ; (BT-CheckInfer () refl) ; (BT-Sub () _)}
checkType Γ (ƛ x ⋯> t) TBool = no λ{(BT-CheckInfer () refl) ; (BT-Sub () _)}
checkType Γ (ƛ x ⋯> a) Top = no λ{(BT-CheckInfer () refl) ; (BT-Sub () _)}
checkType Γ (ƛ x ⋯> a) (′′ X) = no λ{(BT-CheckInfer () refl) ; (BT-Sub () _)}
checkType Γ (ƛ x ⋯> a) (Φ X <: T ∶ U) = no λ{(BT-CheckInfer () refl) ; (BT-Sub () _)}
checkType Γ (Λ X <: T ⋯> U) TBool = no λ{(BT-CheckInfer () refl) ; (BT-Sub () _)}
checkType Γ (Λ X <: T ⋯> U) (A ⇨ B) = no λ{(BT-CheckInfer () refl) ; (BT-Sub () _)}
checkType Γ (Λ X <: T ⋯> U) Top = no λ{(BT-CheckInfer () refl) ; (BT-Sub () _)}
checkType Γ (Λ X <: T ⋯> U) (′′ Y) = no λ{(BT-CheckInfer () refl) ; (BT-Sub () _)}
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

{-# TERMINATING #-}
isSubType Γ TBool TBool = yes S-Refl
isSubType Γ TBool (A ⇨ B) = no imp-TBool<:⇨
isSubType Γ TBool Top = yes S-Top
isSubType Γ TBool (′′ X) = no imp-TBool<:′′
isSubType Γ TBool (Φ x <: T ∶ T₁) = no imp-TBool<:Φ
isSubType Γ (A ⇨ B) TBool = no imp-⇨<:TBool
isSubType Γ (A ⇨ B) Top = yes S-Top
isSubType Γ (A ⇨ B) (′′ x) = no imp-⇨<:′′
isSubType Γ (A ⇨ B) (Φ x <: T ∶ T₁) = no imp-⇨<:Φ
isSubType Γ (S₁ ⇨ S₂) (T₁ ⇨ T₂) with isSubType Γ T₁ S₁ | isSubType Γ S₂ T₂
... | yes T₁<:S₁ | yes S₂<:T₂ = yes (S-Arrow T₁<:S₁ S₂<:T₂)
... | no ¬T₁<:S₁ | _ = no λ{S-Refl → ¬T₁<:S₁ S-Refl ; (S-Trans c c₁) → {!!} ; (S-Arrow T₁<:S₁ _) → ¬T₁<:S₁ T₁<:S₁}
... | _ | no ¬S₂<:T₂ = no λ{S-Refl → ¬S₂<:T₂ S-Refl ; (S-Trans c c₁) → {!!} ; (S-Arrow _ S₂<:T₂) → ¬S₂<:T₂ S₂<:T₂}
isSubType Γ Top TBool = no imp-Top<:TBool
isSubType Γ Top (A ⇨ B) = no imp-Top<:⇨
isSubType Γ Top Top = yes S-Refl
isSubType Γ Top (′′ x) = no imp-Top<:′′
isSubType Γ Top (Φ x <: T ∶ T₁) = no imp-Top<:Φ
isSubType Γ (′′ X) T with T ≟Tp Top | T ≟Tp ′′ X
... | yes refl | _ = yes S-Top
... | _ | yes refl = yes S-Refl
... | no T≠Top | no T≠X with lookup<: Γ X
...   | no ¬X<:S∈Γ = no λ{S-Refl → T≠X refl ; (S-Trans c c₁) → {!!} ; S-Top → T≠Top refl ; (S-TVar X<:T∈Γ) → ¬X<:S∈Γ (T , X<:T∈Γ)}
...   | yes (S , X<:S∈Γ) with S ≟Tp ′′ X
--      TODO: X <: ′′ X should be made impossible and thus lead to a contradiction
...     | yes refl = no λ{c → {!!}}
--      TODO: termination checker is bothered by this call, is it possible to create cycles if X <: ′′ X ∈ Γ is disallowed?
...     | no S≠X with isSubType Γ S T
...       | yes S<:T = yes (S-Trans (S-TVar X<:S∈Γ) S<:T)
...       | no ¬S<:T = no λ{S-Refl → T≠X refl ; (S-Trans c c₁) → {!!} ; S-Top → T≠Top refl ; (S-TVar X<:T∈Γ) → helper4 (uniq-<:∈ X<:S∈Γ X<:T∈Γ) ¬S<:T}
isSubType Γ (Φ X <: T ∶ U) TBool = no imp-Φ<:TBool
isSubType Γ (Φ X <: T ∶ U) (A ⇨ B) = no imp-Φ<:⇨
isSubType Γ (Φ X <: T ∶ U) Top = yes S-Top
isSubType Γ (Φ X <: T ∶ U) (′′ Y) = no imp-Φ<:′′
isSubType Γ (Φ X₁ <: U₁ ∶ S) (Φ X₂ <: U₂ ∶ T) with X₁ ≟ X₂ | U₁ ≟Tp U₂ | isSubType (Γ , X₁ <: U₁) S T
... | yes refl | yes refl | yes S<:T = yes (S-All S<:T)
... | no X₁≠X₂ | _ | _ = no λ{S-Refl → X₁≠X₂ refl ; (S-Trans c c₁) → {!!} ; (S-All _) → X₁≠X₂ refl}
... | _ | no U₁≠U₂ | _ = no λ{S-Refl → U₁≠U₂ refl ; (S-Trans c c₁) → {!!} ; (S-All _) → U₁≠U₂ refl}
... | _ | _ | no ¬S<:T = no λ{S-Refl → ¬S<:T S-Refl ; (S-Trans c c₁) → {!!} ; (S-All S<:T) → ¬S<:T S<:T}

test1 = isSubType ∅ TBool TBool

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
