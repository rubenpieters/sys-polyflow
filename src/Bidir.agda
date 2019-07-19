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
infix 45 _↑
infixl 40 _∙_
infixl 40 _[_]
infix 35 if_then_else
infix 30 ƛ_⋯>_
infix 30 Λ_<:_⋯>_

data Term⁺ : Set
data Term⁻ : Set

data Term⁺ where
  -- variables
  ′_ : Id → Term⁺
  -- application
  _∙_ : Term⁺ → Term⁻ → Term⁺
  -- type application
  _[_] : Term⁺ → Type → Term⁺
  -- annotation
  _↓_ : Term⁻ → Type → Term⁺
  -- bool literals
  B′_ : Bool → Term⁺


data Term⁻ where
  -- if expr
  if_then_else : Term⁺ → Term⁻ → Term⁻ → Term⁻
  -- function abstraction
  ƛ_⋯>_ : Id → Term⁻ → Term⁻
  -- type abstraction
  Λ_<:_⋯>_ : Id → Type → Term⁻ → Term⁻
  -- lift
  _↑ : Term⁺ → Term⁻

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
  S-All : ∀ {Γ X U₁ S₂ T₂}
    → Γ , X <: U₁ ⊢ S₂ <: T₂
    → Γ ⊢ (Φ X <: U₁ ∶ S₂) <: (Φ X <: U₁ ∶ T₂)

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
    → Γ ⊢ t ↑ ⇐ B
  BT-Sub : ∀ {Γ t A B}
    → Γ ⊢ t ⇒ A
    → Γ ⊢ A <: B
    → Γ ⊢ t ↑ ⇐ B

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

dom≡ : ∀ {A A′ B B′} → A ⇨ B ≡ A′ ⇨ B′ → A ≡ A′
dom≡ refl = refl

rng≡ : ∀ {A A′ B B′} → A ⇨ B ≡ A′ ⇨ B′ → B ≡ B′
rng≡ refl = refl

Φ≡ : ∀ {X X' T T' U U'}
  → Φ X <: T ∶ U ≡ Φ X' <: T' ∶ U'
  → X ≡ X' × T ≡ T' × U ≡ U'
Φ≡ refl = (refl , refl , refl)

TBool≠⇨ : ∀ {A B}
  → TBool ≢ A ⇨ B
TBool≠⇨ ()

TBool≠Φ : ∀ {X T U}
  → TBool ≢ Φ X <: T ∶ U
TBool≠Φ ()

uniq-∈ : ∀ {x A B Γ}
  → x ∶ A ∈ Γ
  → x ∶ B ∈ Γ
  → A ≡ B
uniq-∈ Z: Z: = refl
uniq-∈ Z: (S: x≠x _) = ⊥-elim (x≠x refl)
uniq-∈ (S: x≠x _) Z: = ⊥-elim (x≠x refl)
uniq-∈ (S: _ x:A∈Γ) (S: _ x:B∈Γ) = uniq-∈ x:A∈Γ x:B∈Γ
uniq-∈ (S:-Skip<: x:A∈Γ) (S:-Skip<: x:B∈Γ) = uniq-∈ x:A∈Γ x:B∈Γ

uniq-⇒ : ∀ {Γ t A B}
  → Γ ⊢ t ⇒ A
  → Γ ⊢ t ⇒ B
  → A ≡ B
uniq-⇒ (BT-Var x:A∈Γ) (BT-Var x:B∈Γ) = uniq-∈ x:A∈Γ x:B∈Γ
uniq-⇒ BT-True BT-True = refl
uniq-⇒ BT-False BT-False = refl
uniq-⇒ (BT-App t₁⇒A₁⇨B₁ _) (BT-App t₁⇒A₂⇨B₂ _) = rng≡ (uniq-⇒ t₁⇒A₁⇨B₁ t₁⇒A₂⇨B₂)
uniq-⇒ (BT-Ann _) (BT-Ann _) = refl
uniq-⇒ (BT-TApp t⇒Φ₁ Y<:T₁) (BT-TApp t⇒Φ₂ Y<:T₂) with Φ≡ (uniq-⇒ t⇒Φ₁ t⇒Φ₂)
... | (refl , refl , refl) = refl

ext∈ : ∀ {x y Γ B}
  → (x ≢ y)
  → ¬ ∃[ A ](x ∶ A ∈ Γ)
  → ¬ ∃[ A ](x ∶ A ∈ Γ , y ∶ B)
ext∈ x≠y ¬x:A∈Γ (A , Z:) = x≠y refl
ext∈ x≠y ¬x:A∈Γ (A , S: _ x:A∈Γ) = ¬x:A∈Γ (A , x:A∈Γ)

ext∈<: : ∀ {x Γ S T}
  → ¬ ∃[ A ](x ∶ A ∈ Γ)
  → ¬ ∃[ A ](x ∶ A ∈ Γ , S <: T)
ext∈<: ¬x:A∈Γ (A , S:-Skip<: x:A∈Γ) = ¬x:A∈Γ (A , x:A∈Γ)

lookup : (Γ : Context) → (x : Id)
  → Dec (∃[ A ](x ∶ A ∈ Γ))
lookup ∅ x = no (λ ())
lookup (Γ , y ∶ B) x with x ≟ y
... | yes refl = yes (B , Z:)
... | no x≠y with lookup Γ x
...   | no ¬x:A∈Γ = no (ext∈ x≠y ¬x:A∈Γ)
...   | yes (A , x:A∈Γ) = yes (A , S: x≠y x:A∈Γ)
lookup (Γ , _ <: _) x with lookup Γ x
... | yes (A , x:A∈Γ) = yes (A , S:-Skip<: x:A∈Γ)
... | no ¬x:A∈Γ = no (ext∈<: ¬x:A∈Γ)

app-arg-wrong-type : ∀ {Γ t₁ t₂ A B}
  → Γ ⊢ t₁ ⇒ A ⇨ B
  → ¬ Γ ⊢ t₂ ⇐ A
  → ¬ ∃[ B' ](Γ ⊢ t₁ ∙ t₂ ⇒ B')
app-arg-wrong-type t₁⇒A⇨B ¬t₂⇐A (B' , BT-App t₁⇒A'⇨B' t₂⇐A') with dom≡ (uniq-⇒ t₁⇒A⇨B t₁⇒A'⇨B')
... | refl = ¬t₂⇐A t₂⇐A'

inferType :
    (Γ : Context)
  → (t : Term⁺)
  → Dec (∃[ A ](Γ ⊢ t ⇒ A))

checkType :
    (Γ : Context)
  → (t : Term⁻)
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
... | yes (TBool , t₁⇒TBool) = no λ{(B , BT-App t₁⇒A⇨B t₂⇐A) → TBool≠⇨ (uniq-⇒ t₁⇒TBool t₁⇒A⇨B)}
... | yes (Top , b) = {!!}
... | yes (′′ x , b) = {!!}
... | yes (Φ x <: t ∶ t₃ , b) = {!!}
... | yes (A ⇨ B , t₁⇒A⇨B) with checkType Γ t₂ A
...   | no ¬t₂⇐A = no (app-arg-wrong-type t₁⇒A⇨B ¬t₂⇐A)
...   | yes t₂⇐A = yes (B , BT-App t₁⇒A⇨B t₂⇐A)
inferType Γ (t ↓ T) with checkType Γ t T
... | yes t⇐T = yes (T , BT-Ann t⇐T)
... | no ¬t⇐T = no λ{(_ , BT-Ann t⇐T) → ¬t⇐T t⇐T}
inferType Γ (B′ true) = yes (TBool , BT-True)
inferType Γ (B′ false) = yes (TBool , BT-False)
inferType Γ (t [ Y ]) with inferType Γ t
... | no z = {!!}
... | yes (TBool , t⇒TBool) = no λ{(_ , BT-TApp t⇒Φ _) → TBool≠Φ (uniq-⇒ t⇒TBool t⇒Φ)}
... | yes (a ⇨ a₁ , b) = {!!}
... | yes (Top , b) = {!!}
... | yes (′′ x , b) = {!!}
... | yes (Φ X <: T ∶ U , t⇒Φ) with isSubType Γ Y T
...   | no ¬Y<:T = no λ{(_ , BT-TApp t⇒Φ' Y<:T) → {!uniq-⇒ t⇒Φ t⇒Φ!}}
...   | yes Y<:T = yes (U [ X τ= Y ] , BT-TApp t⇒Φ Y<:T)

checkType Γ (if t₁ then t₂ else t₃) T with inferType Γ t₁
... | no ¬t₁⇒T = no λ{(BT-If t₁⇒TBool _ _) → ¬t₁⇒T (TBool , t₁⇒TBool)}
... | yes (A ⇨ B , t₁⇒A⇨B) = no λ{(BT-If t₁⇒TBool _ _) → TBool≠⇨ (uniq-⇒ t₁⇒TBool t₁⇒A⇨B)}
... | yes (TBool , t₁⇒TBool) with checkType Γ t₂ T | checkType Γ t₃ T
...   | yes t₂⇐T | yes t₃⇐T = yes (BT-If t₁⇒TBool t₂⇐T t₃⇐T)
...   | no ¬t₂⇐T | _ = no λ{(BT-If _ t₂⇐T _) → ¬t₂⇐T t₂⇐T}
...   | yes _ | no ¬t₃⇐T = no λ{(BT-If _ _ t₃⇐T) → ¬t₃⇐T t₃⇐T}
checkType Γ (ƛ x ⋯> t) (A ⇨ B) with checkType (Γ , x ∶ A) t B
... | yes t⇐B = yes (BT-Abs t⇐B)
... | no ¬t⇐B = no λ{(BT-Abs t⇐B) → ¬t⇐B t⇐B}
checkType Γ (ƛ x ⋯> t) TBool = no λ()
checkType Γ (ƛ x ⋯> a) Top = yes {!!}
checkType Γ (ƛ x ⋯> a) (′′ X) = no λ()
checkType Γ (ƛ x ⋯> a) (Φ X <: T ∶ U) = no λ()
checkType Γ (t ↑) A with inferType Γ t
-- ... | no ¬t⇒A = no λ{(BT-CheckInfer t⇒A _) → ¬t⇒A (_ , t⇒A)}
... | no ¬t⇒A = no λ{(BT-CheckInfer t⇒A _) → ¬t⇒A (_ , t⇒A) ; (BT-Sub t⇒A _) → ¬t⇒A (_ , t⇒A)}
... | yes (B , t⇒B) with A ≟Tp B
...   | yes refl = yes (BT-CheckInfer t⇒B refl)
...   | no A≠B = no λ{(BT-CheckInfer t⇒A refl) → A≠B (uniq-⇒ t⇒A t⇒B)}
checkType Γ (Λ x <: x₁ ⋯> a) b = {!!}

isSubType Γ S T = {!!}


test_prog1 : Term⁺
test_prog1 = ((ƛ "x" ⋯> ′"x"↑)↓ TBool ⇨ TBool) ∙ (B′ true ↑)

test_infer1 : inferType ∅ test_prog1 ≡ yes (TBool , _)
test_infer1 = refl

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
