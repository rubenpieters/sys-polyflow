module Lang where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym)
open import Data.String using (String; _≟_)
open import Data.Bool using (Bool; true; false)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (∃; _,_; _×_)
open import Data.Unit using (⊤; tt)


Id : Set
Id = String

-- -------------------------------------
-- TYPES

infix 55 _∨_
infix 50 _⇒_
infix 50 ′′_
infix 40 A_<:_∶_
infix 40 [T=_,F=_][_]

data Type : Set where
  TTrue : Type
  TFalse : Type
  _⇒_ : Type → Type → Type
  ′′_ : Id → Type
  A_<:_∶_ : Id → Type → Type → Type
  Top : Type
  _∨_ : Type → Type → Type
  [T=_,F=_][_] : Type → Type → Type → Type

TBool : Type
TBool = TTrue ∨ TFalse

-- -------------------------------------

-- -------------------------------------
-- TERMS

infix 50 ′_
infix 50 B′_
infixl 40 _∙_
infixl 40 _[_]
infix 35 if_then_else
infix 32 _===_
infix 30 ƛ_∶_⋯>_∶_
infix 30 Λ_<:_⋯>_

data Term : Set where
  -- variables
  ′_ : Id → Term
  -- bool literals
  B′_ : Bool → Term
  -- if expr
  if_then_else : Term → Term → Term → Term
  -- function abstraction
  ƛ_∶_⋯>_∶_ : Id → Type → Term → Type → Term
  -- application
  _∙_ : Term → Term → Term
  -- type abstraction
  Λ_<:_⋯>_ : Id → Type → Term → Term
  -- type application
  _[_] : Term → Type → Term
  -- equality check
  _===_ : Term → Term → Term

prog1 : Term
prog1 =
  (ƛ "f" ∶ TBool ⇒ TBool ⋯> (ƛ "x" ∶ TBool ⋯> ′"f" ∙ ′"x" ∶ TBool) ∶ TBool ⇒ TBool) ∙
  (ƛ "x" ∶ TBool ⋯> if ′"x" then (B′ true) else (B′ false) ∶ TBool) ∙
  B′ true

-- -------------------------------------

-- -------------------------------------
-- CONTEXT

-- definition

infixl 50 _,_∶_
infixl 50 _,_<:_
infixl 50 _,T<:_
infixl 50 _,F<:_

data Context : Set where
  ∅ : Context
  _,_∶_ : Context → Id → Type → Context
  _,_<:_ : Context → Id → Type → Context
  _,T<:_ : Context → Id → Context
  _,F<:_ : Context → Id → Context

-- has-type-in-context relation

data _∶_∈_ : Id → Type → Context → Set where
  Z : ∀ {x T Γ}
    → x ∶ T ∈ Γ , x ∶ T
  S : ∀ {x T Γ y U}
    → x ≢ y
    → x ∶ T ∈ Γ
    → x ∶ T ∈ Γ , y ∶ U

-- is-subtype-in-context relation

data _<:_∈_ : Id → Type → Context → Set where
  Z<: : ∀ {Γ X T}
    → X <: T ∈ Γ , X <: T
  S<: : ∀ {Γ X T Y U}
    → X ≢ Y
    → X <: T ∈ Γ
    → X <: T ∈ Γ , Y <: U

-- is-supertype-in-context relation

data T<:_∈_ : Id → Context → Set where
  ZT<: : ∀ {Γ X}
    → T<: X ∈ (Γ ,T<: X)

data F<:_∈_ : Id → Context → Set where
  ZF<: : ∀ {Γ X}
    → F<: X ∈ (Γ ,F<: X)


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
  S-TVarSub : ∀ {Γ X T}
    → X <: T ∈ Γ
    → Γ ⊢ ′′ X <: T
  S-TVarSupT : ∀ {Γ X}
    → T<: X ∈ Γ
    → Γ ⊢ TTrue <: ′′ X
  S-TVarSupF : ∀ {Γ X}
    → F<: X ∈ Γ
    → Γ ⊢ TFalse <: ′′ X
  S-Arrow : ∀ {Γ S₁ S₂ T₁ T₂}
    → Γ ⊢ T₁ <: S₁
    → Γ ⊢ S₂ <: T₂
    → Γ ⊢ S₁ ⇒ S₂ <: T₁ ⇒ T₂
  S-All : ∀ {Γ X U₁ S₂ T₂}
    → Γ , X <: U₁ ⊢ S₂ <: T₂
    → Γ ⊢ (A X <: U₁ ∶ S₂) <: (A X <: U₁ ∶ T₂)
  S-UnionL : ∀ {Γ A B}
    → Γ ⊢ A <: A ∨ B
  S-UnionR : ∀ {Γ A B}
    → Γ ⊢ B <: A ∨ B
  S-MapTrueL : ∀ {Γ T₁ T₂}
    → Γ ⊢ [T= T₁ ,F= T₂ ][ TTrue ] <: T₁
  S-MapTrueR : ∀ {Γ T₁ T₂}
    → Γ ⊢ T₁ <: [T= T₁ ,F= T₂ ][ TTrue ]
  S-MapFalseL : ∀ {Γ T₁ T₂}
    → Γ ⊢ [T= T₁ ,F= T₂ ][ TFalse ] <: T₂
  S-MapFalseR : ∀ {Γ T₁ T₂}
    → Γ ⊢ T₂ <: [T= T₁ ,F= T₂ ][ TFalse ]
  S-MapBoolL : ∀ {Γ T₁ T₂}
    → Γ ⊢ [T= T₁ ,F= T₂ ][ TBool ] <: T₁ ∨ T₂
  S-Map : ∀ {Γ S T T₁ T₂}
    → Γ ⊢ S <: T
    → Γ ⊢ [T= T₁ ,F= T₂ ][ S ] <: [T= T₁ ,F= T₂ ][ T ]

data _⊢_≅_ : Context → Type → Type → Set where
  Sim : ∀ {Γ A B}
    → Γ ⊢ A <: B
    → Γ ⊢ B <: A
    → Γ ⊢ A ≅ B
{-
False <: True is possible in some contexts, thus ∀ {Γ} → Γ ⊢ TFalse <: TTrue → ⊥ is not provable

consider:

function f<X extends "true">(x: X) {
  if (x === "true") {
    // ...
  } else {
    // In this block, we have both Γ ⊢ X <: True and Γ ⊢ False <: X
    // Thus, by S-Trans we have Γ ⊢ False <: True
    // Within this block we are able to use Γ ⊢ false : True but the code is unreachable
  }
}
-}

swap-≅ : ∀ {Γ A B}
  → Γ ⊢ A ≅ B
  → Γ ⊢ B ≅ A
swap-≅ (Sim a b) = Sim b a

trans-≅ : ∀ {Γ A B C}
  → Γ ⊢ A ≅ B
  → Γ ⊢ B ≅ C
  → Γ ⊢ A ≅ C
trans-≅ (Sim A<:B B<:A) (Sim B<:C C<:B) = Sim (S-Trans A<:B B<:C) (S-Trans C<:B B<:A)

-- inversion of subtyping relation

inversion-<:-var2 : ∀ {Γ S U X}
  → Γ ⊢ S <: U
  → Γ ⊢ U ≅ ′′ X
  → (∃ λ Y → Γ ⊢ S ≅ ′′ Y) ⊎ Γ ⊢ S ≅ TTrue ⊎ Γ ⊢ S ≅ TFalse

inversion-<:-true : ∀ {Γ S}
  → Γ ⊢ S <: TTrue
  → (∃ λ X → Γ ⊢ S ≅ ′′ X) ⊎ Γ ⊢ S ≅ TTrue ⊎ Γ ⊢ S ≅ TFalse

inversion-<:-true2 : ∀ {Γ S U}
  → Γ ⊢ S <: U
  → Γ ⊢ U ≅ TTrue
  → (∃ λ X → Γ ⊢ S ≅ ′′ X) ⊎ Γ ⊢ S ≅ TTrue ⊎ Γ ⊢ S ≅ TFalse

-- if S is a subtype of ′′X in Γ, then:
-- 1. S is similar to a type variable
-- 2. S is True
-- 3. S is False
{-# TERMINATING #-}
inversion-<:-var : ∀ {Γ S X}
  → Γ ⊢ S <: ′′ X
  → (∃ λ Y → Γ ⊢ S ≅ ′′ Y) ⊎ Γ ⊢ S ≅ TTrue ⊎ Γ ⊢ S ≅ TFalse
-- in case of S-Refl, then trivially S is a type variable
inversion-<:-var {X = X} (S-Refl) = inj₁ (X , (Sim S-Refl S-Refl))
-- in case of S-Trans, then by induction U is a type variable
-- then again by induction S is a type variable
inversion-<:-var (S-Trans S<:U U<:′′X) with inversion-<:-var U<:′′X
... | inj₁ (Y , U≅′′Y) = inversion-<:-var2 S<:U U≅′′Y
... | inj₂ (inj₂ U≅False) = {!!}
... | inj₂ (inj₁ U≅True) = inversion-<:-true2 S<:U U≅True
-- in case of S-TVar, then trivially S is a type variable
inversion-<:-var (S-TVarSub {X = X} _) = inj₁ (X , (Sim S-Refl S-Refl))
inversion-<:-var {X = X} S-MapTrueL = inj₁ (X , Sim S-MapTrueL S-MapTrueR)
inversion-<:-var {X = X} S-MapFalseL = inj₁ (X , Sim S-MapFalseL S-MapFalseR)
inversion-<:-var (S-TVarSupT _) = inj₂ (inj₁ (Sim S-Refl S-Refl))
inversion-<:-var (S-TVarSupF _) = inj₂ (inj₂ (Sim S-Refl S-Refl))

inversion-<:-true S-Refl = inj₂ (inj₁ (Sim S-Refl S-Refl))
inversion-<:-true (S-Trans S<:U U<:TTrue) with inversion-<:-true U<:TTrue
... | inj₂ (inj₁ U≅True) = inversion-<:-true2 S<:U U≅True
... | inj₂ (inj₂ U≅False) = {!!}
... | inj₁ (Y , U≅′′Y) = inversion-<:-var2 S<:U U≅′′Y
inversion-<:-true (S-TVarSub {X = X} X<:TTrue) = inj₁ (X , (Sim S-Refl S-Refl))
inversion-<:-true S-MapTrueL = inj₂ (inj₁ (Sim S-MapTrueL S-MapTrueR))
inversion-<:-true S-MapFalseL = inj₂ (inj₁ (Sim S-MapFalseL S-MapFalseR))

inversion-<:-var2 a (Sim S-Refl y) = inversion-<:-var a
inversion-<:-var2 S<:U (Sim (S-Trans U<:T T<:′′X) ′′X<:U) with inversion-<:-var T<:′′X
-- ... | inj₁ (Y , Sim T<:′′Y ′′Y<:T) = inversion-<:-var (S-Trans (S-Trans S<:U U<:T) T<:′′Y)
... | inj₂ (inj₂ y) = {!!}
... | inj₁ (Y , T≅′′Y) = {!!} -- with inversion-<:-var2 U<:T T≅′′Y
--...   | c = {!!}
... | inj₂ (inj₁ T≅TTrue) with inversion-<:-true2 U<:T T≅TTrue
...   | inj₁ (_ , U≅′′Z) = inversion-<:-var2 S<:U U≅′′Z
...   | inj₂ (inj₁ U≅TTrue) = inversion-<:-true2 S<:U U≅TTrue
...   | inj₂ (inj₂ U≅TFalse) = {!!}
inversion-<:-var2 a (Sim (S-TVarSub x) y) = {!!}
inversion-<:-var2 a (Sim (S-TVarSupT x) y) = inversion-<:-true a
inversion-<:-var2 a (Sim (S-TVarSupF x) y) = {!!}
inversion-<:-var2 a (Sim S-MapTrueL y) = inversion-<:-var (S-Trans a S-MapTrueL)
inversion-<:-var2 a (Sim S-MapFalseL y) = inversion-<:-var (S-Trans a S-MapFalseL)

inversion-<:-true2 a (Sim S-Refl y) = inversion-<:-true a
inversion-<:-true2 a (Sim (S-Trans x y) z) with inversion-<:-true2 x (Sim y (S-Trans z x))
... | inj₂ (inj₁ U≅True) = inversion-<:-true2 a U≅True
... | inj₂ (inj₂ U≅False) = {!!}
... | inj₁ (Y , U≅′′Y) = inversion-<:-var2 a U≅′′Y
inversion-<:-true2 a (Sim (S-TVarSub x) y) = inversion-<:-var a
inversion-<:-true2 a (Sim S-MapTrueL y) = inversion-<:-true2 a (Sim S-MapTrueL S-MapTrueR)
inversion-<:-true2 a (Sim S-MapFalseL y) = inversion-<:-true2 a (Sim S-MapFalseL S-MapFalseR)

{-
inversion-<:-false : ∀ {Γ S}
  → Γ ⊢ S <: TFalse
  → (∃ λ X → S ≡ ′′ X) ⊎ S ≡ TFalse
inversion-<:-false S-Refl = inj₂ refl
inversion-<:-false (S-Trans S<:U U<:TFalse) with inversion-<:-false U<:TFalse
... | inj₁ (_ , refl) = inj₁ (inversion-<:-var S<:U)
... | inj₂ refl = inversion-<:-false S<:U
inversion-<:-false (S-TVarSub {X = X} X<:TFalse) = inj₁ (X , refl)

-- if S is a subtype of TBool, then S is a type variable or TBool/TTrue/TFalse
inversion-<:-bool : ∀ {Γ S}
  → Γ ⊢ S <: TBool
  → (∃ λ X → S ≡ ′′ X) ⊎ S ≡ TBool ⊎ S ≡ TTrue ⊎ S ≡ TFalse
-- in case of S-Refl, then trivially S is TBool
inversion-<:-bool (S-Refl) = inj₂ (inj₁ refl)
-- in case of S-Trans, then by induction U is either a type variable or TBool
inversion-<:-bool (S-Trans S<:U U<:TBool) with inversion-<:-bool U<:TBool
-- if U is a type variable, then S is a type variable
... | inj₁ (_ , refl) = inj₁ (inversion-<:-var S<:U)
-- if U is TBool, then by induction S is a type variable or TBool
... | inj₂ (inj₁ refl) = inversion-<:-bool S<:U
... | inj₂ (inj₂ (inj₁ refl)) with inversion-<:-true S<:U
...   | inj₁ (X , refl) = inj₁ (X , refl)
...   | inj₂ refl = inj₂ (inj₂ (inj₁ refl))
inversion-<:-bool (S-Trans S<:U U<:TBool) | inj₂ (inj₂ (inj₂ refl)) with inversion-<:-false S<:U
...   | inj₁ (X , refl) = inj₁ (X , refl)
...   | inj₂ refl = inj₂ (inj₂ (inj₂ refl))
-- in case of S-TVar, then trivially S is a type variable
inversion-<:-bool (S-TVarSub {X = X} _) = inj₁ (X , refl)
inversion-<:-bool (S-UnionL) = inj₂ (inj₂ (inj₁ refl))
inversion-<:-bool (S-UnionR) = inj₂ (inj₂ (inj₂ refl))

-- if S is a subtype of T₁ ⇒ T₂, then S is a type variable or S has the form S₁ ⇒ S₂ (with T₁ a subtype of S₁ and S₂ a subtype of T₂)
inversion-<:-abs : ∀ {Γ S T₁ T₂}
  → Γ ⊢ S <: T₁ ⇒ T₂
  → (∃ λ X → S ≡ ′′ X) ⊎ (∃ λ S₁ → ∃ λ S₂ → Γ ⊢ T₁ <: S₁ × Γ ⊢ S₂ <: T₂ × S ≡ S₁ ⇒ S₂)
-- in case of S-Refl, then trivially S has the form S₁ ⇒ S₂
inversion-<:-abs {T₁ = T₁} {T₂ = T₂} (S-Refl) = inj₂ (T₁ , T₂ , S-Refl , S-Refl , refl)
-- in case of S-Trans, then by induction U is either a type variable or has the form U₁ ⇒ U₂
inversion-<:-abs (S-Trans S<:U U<:T₁⇒T₂) with inversion-<:-abs U<:T₁⇒T₂
-- if U is a type variable, then S is a type variable
... | inj₁ (_ , refl) = inj₁ (inversion-<:-var S<:U)
-- if U has the form U₁ ⇒ U₂, then by induction S is either a type variable or has the form S₁ ⇒ S₂
... | inj₂ (U₁ , U₂ , T₁<:U₁ , U₂<:T₂ , refl) with inversion-<:-abs S<:U
-- if S is a type variable, then trivially S is a type variable
...   | inj₁ (X , refl) = inj₁ (X , refl)
-- if S has the form S₁ ⇒ S₂, then it trivially has the form S₁ ⇒ S₂
-- the subtyping constraints T₁ <: S₁ and T₂ <: S₂ are satisfied by transitivity of subtyping via U₁ and U₂
...   | inj₂ (S₁ , S₂ , U₁<:S₁ , S₂<:U₂ , refl) = inj₂ (S₁ , S₂ , S-Trans T₁<:U₁ U₁<:S₁ , S-Trans S₂<:U₂ U₂<:T₂ , refl)
-- in case of S-TVar, then trivially S is a type variable
inversion-<:-abs (S-TVarSub {X = X} _) = inj₁ (X , refl)
-- in case of S-Arrow, then trivially S has the form S₁ ⇒ S₂
inversion-<:-abs (S-Arrow {S₁ = S₁} {S₂ = S₂} T₁<:S₁ S₂<:T₂) = inj₂ (S₁ , S₂ , T₁<:S₁ , S₂<:T₂ , refl)

-- if S is a subtype of A X <: U₁ : T₂, then S is a type variable or S has the form A X <: U₁ : S₂ (with S₂ a subtype of T₂)
inversion-<:-forall : ∀ {Γ S U₁ T₂ X}
  → Γ ⊢ S <: A X <: U₁ ∶ T₂
  → (∃ λ X → S ≡ ′′ X) ⊎ (∃ λ S₂ → Γ , X <: U₁ ⊢ S₂ <: T₂ × S ≡ A X <: U₁ ∶ S₂)
-- in case of S-Refl, then trivially S has the form A X <: U₁ : T₂
inversion-<:-forall {T₂ = T₂} (S-Refl) = inj₂ (T₂ , S-Refl , refl)
-- in case of S-Trans, then by induction U is either a type variable or has the form A X <: U₁ : T₂
inversion-<:-forall (S-Trans S<:U U<:AX<:U₁:T₂) with inversion-<:-forall U<:AX<:U₁:T₂
-- if U is a type variable, then S is a type variable
... | inj₁ (_ , refl) = inj₁ (inversion-<:-var S<:U)
-- if U has the form A X <: U₁ : T₂, then by induction S is either a type variable or has the form A X <: U₁ : T₂
... | inj₂ (U₂ , (U₂<:T₂ , refl)) with inversion-<:-forall S<:U
-- if S is a type variable, then trivially S is a type variable
...  | inj₁ (X , refl) = inj₁ (X , refl)
-- if S has the form A X <: U₁ : T₂, then it trivially has the form A X <: U₁ : T₂
-- the subtyping constraint T₂ <: S₂ is satisfied by transitivity of subtyping via U₂
...  | inj₂ (S₂ , (S₂<:U₂ , refl)) = inj₂ (S₂ , S-Trans S₂<:U₂ U₂<:T₂ , refl)
-- in case of S-TVar, then trivially S is a type variable
inversion-<:-forall (S-TVarSub {X = X} _) = inj₁ (X , refl)
-- in case of S-All, then trivially S has the form A X <: U₁ : S₂
inversion-<:-forall (S-All {S₂ = S₂} S₂<:T₂) = inj₂ (S₂ , S₂<:T₂ , refl)

-- -------------------------------------

-- -------------------------------------
-- TYPING RELATION

-- type substitution

infix 50 _[_τ=_]

_[_τ=_] : Type → Id → Type → Type
(′′ x) [ y τ= s ] with x ≟ y
... | yes _ = s
... | no _ = ′′ x
TTrue [ y τ= s ] = TTrue
TFalse [ y τ= s ] = TFalse
(x ⇒ x₁) [ y τ= s ] = (x [ y τ= s ]) ⇒ (x₁ [ y τ= s ])
(A x <: X ∶ x₁) [ y τ= s ] = A x <: (X [ y τ= s ]) ∶ x₁ [ y τ= s ]
Top [ y τ= s ] = Top
(a ∨ b) [ y τ= s ] = (a [ y τ= s ]) ∨ (b [ y τ= s ])
[T= a ,F= b ][ x ] [ y τ= s ] = [T= a [ y τ= s ] ,F= b [ y τ= s ] ][ x [ y τ= s ] ]

-- typing relation

data _⊢_∶_ : Context → Term → Type → Set where
  T-Var : ∀ {Γ x T}
    → x ∶ T ∈ Γ
    → Γ ⊢ ′ x ∶ T
  T-Abs : ∀ {Γ x t₂ T₁ T₂}
    → Γ , x ∶ T₁ ⊢ t₂ ∶ T₂
    → Γ ⊢ (ƛ x ∶ T₁ ⋯> t₂ ∶ T₂) ∶ T₁ ⇒ T₂
  T-App : ∀ {Γ t₁ t₂ T₁₁ T₁₂}
    → Γ ⊢ t₁ ∶ T₁₁ ⇒ T₁₂
    → Γ ⊢ t₂ ∶ T₁₁
    → Γ ⊢ t₁ ∙ t₂ ∶ T₁₂
  T-True : ∀ {Γ}
    → Γ ⊢ B′ true ∶ TTrue
  T-False : ∀ {Γ}
    → Γ ⊢ B′ false ∶ TFalse
  T-If : ∀ {Γ T t₁ t₂ t₃}
    → Γ ⊢ t₁ ∶ TBool
    → Γ ⊢ t₂ ∶ T
    → Γ ⊢ t₃ ∶ T
    → Γ ⊢ if t₁ then t₂ else t₃ ∶ T
  T-IfTrueR : ∀ {Γ T t₂ t₃ x X}
    → Γ ⊢ ′ x ∶ ′′ X
    → (Γ ,T<: X) ⊢ t₂ ∶ T
    → Γ ⊢ t₃ ∶ T
    → Γ ⊢ if (′ x === B′ true) then t₂ else t₃ ∶ T
  T-TAbs : ∀ {Γ X t₂ T₁ T₂}
    → Γ , X <: T₁ ⊢ t₂ ∶ T₂
    → Γ ⊢ Λ X <: T₁ ⋯> t₂ ∶ A X <: T₁ ∶ T₂
  T-TApp : ∀ {Γ t₁ X T₁₁ T₁₂ T₂}
    → Γ ⊢ t₁ ∶ (A X <: T₁₁ ∶ T₁₂)
    → Γ ⊢ T₂ <: T₁₁
    → Γ ⊢ t₁ [ T₂ ] ∶ T₁₂ [ X τ= T₂ ]
  T-Sub : ∀ {Γ t S T}
    → Γ ⊢ t ∶ S
    → Γ ⊢ S <: T
    → Γ ⊢ t ∶ T
  T-Eq : ∀ {Γ t₁ t₂ T₁ T₂}
    → Γ ⊢ t₁ ∶ T₁
    → Γ ⊢ t₂ ∶ T₂
    → Γ ⊢ t₁ === t₂ ∶ TBool

-- inversion helpers

inversion-:-abs : ∀ {Γ x S₁ s₂ S₂ T U₁ U₂}
  → Γ ⊢ (ƛ x ∶ S₁ ⋯> s₂ ∶ S₂) ∶ T
  → Γ ⊢ T <: U₁ ⇒ U₂
  → Γ ⊢ U₁ <: S₁ × Γ ⊢ S₂ <: U₂ × Γ , x ∶ S₁ ⊢ s₂ ∶ S₂
inversion-:-abs (T-Abs s₂:T₂) T<:U₁⇒U₂ with inversion-<:-abs T<:U₁⇒U₂
... | inj₁ (_ , ())
... | inj₂ (S₁ , S₂ , U₁<:S₁ , S₂<:U₂ , refl) = (U₁<:S₁ , S₂<:U₂ , s₂:T₂)
inversion-:-abs (T-Sub s₂:S S<:T) T<:U₁⇒U₂ = inversion-:-abs s₂:S (S-Trans S<:T T<:U₁⇒U₂)

inversion-:-tabs : ∀ {Γ X Y S₁ s₂ T U₁ U₂}
  → Γ ⊢ Λ X <: S₁ ⋯> s₂ ∶ T
  → Γ ⊢ T <: A Y <: U₁ ∶ U₂
  → ∃ λ S₂ → X ≡ Y × U₁ ≡ S₁ × Γ , X <: S₁ ⊢ s₂ ∶ S₂ × Γ , X <: S₁ ⊢ S₂ <: U₂
inversion-:-tabs (T-TAbs s₂:T₂) T₂<:AX<:U₁∶U₂ with inversion-<:-forall T₂<:AX<:U₁∶U₂
... | inj₁ (_ , ())
... | inj₂ (S₂ , S₂<:U₂ , refl) = (S₂ , refl , refl , s₂:T₂ , S₂<:U₂)
inversion-:-tabs (T-Sub s₂:S S<:T) T<:AX<:U₁∶U₂ = inversion-:-tabs s₂:S (S-Trans S<:T T<:AX<:U₁∶U₂)

-- -------------------------------------

-- -------------------------------------
-- VALUES

data Value : Term → Set where
  V-Abs : ∀ {x T₁ T₂ t}
    → Value (ƛ x ∶ T₁ ⋯> t ∶ T₂)
  V-Bool : ∀ {b}
    → Value (B′ b)
  V-TAbs : ∀ {X t T}
    → Value (Λ X <: T ⋯> t)

data V-Eq : Term → Term → Set where
  Eq-Bool : ∀ {b₁ b₂}
    → b₁ ≡ b₂
    → V-Eq (B′ b₁) (B′ b₂)

v-eq : ∀ {v₁ v₂} → Value v₁ → Value v₂ → V-Eq v₁ v₂ ⊎ ⊤
v-eq (V-Bool {true}) (V-Bool {true}) = inj₁ (Eq-Bool refl)
v-eq (V-Bool {false}) (V-Bool {false}) = inj₁ (Eq-Bool refl)
v-eq _ _ = inj₂ tt

-- -------------------------------------

-- -------------------------------------
-- EVALUATION

-- term term substitution

infix 50 _[_:=_]

_[_:=_] : Term → Id → Term → Term
(′ x) [ y := s ] with x ≟ y
... | yes _ = s
... | no _ = ′ x
(B′ b) [ _ := _ ] = B′ b
(if t₁ then t₂ else t₃) [ y := s ] =
  if (t₁ [ y := s ]) then (t₂ [ y := s ]) else (t₃ [ y := s ])
(ƛ x ∶ T₁ ⋯> t ∶ T₂) [ y := s ] with x ≟ y
... | yes _ = ƛ x ∶ T₁ ⋯> t ∶ T₂
... | no _ = ƛ x ∶ T₁ ⋯> (t [ y := s ]) ∶ T₂
(t₁ ∙ t₂) [ y := s ] = (t₁ [ y := s ]) ∙ (t₂ [ y := s ])
(Λ x <: T₁ ⋯> x₁) [ y := s ] = Λ x <: T₁ ⋯> x₁ [ y := s ]
(x [ x₁ ]) [ y := s ] = (x [ y := s ]) [ x₁ ]
(x₁ === x₂) [ y := s ] = (x₁ [ y := s ]) === (x₂ [ y := s ])

-- term type substitution

infix 50 _[_:τ=_]

_[_:τ=_] : Term → Id → Type → Term
(′ x) [ _ :τ= _ ] = ′ x
(B′ b) [ _ :τ= _ ] = B′ b
(if t₁ then t₂ else t₃) [ y :τ= s ] =
  if (t₁ [ y :τ= s ]) then (t₂ [ y :τ= s ]) else (t₃ [ y :τ= s ])
(ƛ x ∶ T₁ ⋯> t ∶ T₂) [ y :τ= s ] = ƛ x ∶ (T₁ [ y τ= s ]) ⋯> t ∶ T₂
(t₁ ∙ t₂) [ y :τ= s ] = (t₁ [ y :τ= s ]) ∙ (t₂ [ y :τ= s ])
(Λ x <: T₁ ⋯> x₁) [ y :τ= s ] = Λ x <: T₁ ⋯> x₁ [ y :τ= s ]
(x [ x₁ ]) [ y :τ= s ] = x [ x₁ [ y τ= s ] ]
(x₁ === x₂) [ y :τ= s ] = (x₁ [ y :τ= s ]) === (x₂ [ y :τ= s ])

-- evaluation

-- NOTE: these evaluation rules do not check whether the 'v' variables are values

data _—→_ : Term → Term → Set where
  E-App1 : ∀ {t₁ t₁' t₂}
    → t₁ —→ t₁'
    → t₁ ∙ t₂ —→ t₁' ∙ t₂
  E-App2 : ∀ {v₁ t₂ t₂'}
    → t₂ —→ t₂'
    → v₁ ∙ t₂ —→ v₁ ∙ t₂'
  E-AppAbs : ∀ {x T₁₁ t₁₂ T₁₂ v₂}
    → (ƛ x ∶ T₁₁ ⋯> t₁₂ ∶ T₁₂) ∙ v₂ —→ t₁₂ [ x := v₂ ]
  E-IfTrue : ∀ {t₁ t₂}
    → if B′ true then t₁ else t₂ —→ t₁
  E-IfFalse : ∀ {t₁ t₂}
    → if B′ false then t₁ else t₂ —→ t₂
  E-If : ∀ {t t' t₁ t₂}
    → t —→ t'
    → if t then t₁ else t₂ —→ if t' then t₁ else t₂
  E-TApp : ∀ {t₁ t₁' T₂}
    → t₁ —→ t₁'
    → t₁ [ T₂ ] —→ t₁' [ T₂ ]
  E-TAppAbs : ∀ {X T₁ t₁₂ T₂}
    → (Λ X <: T₁ ⋯> t₁₂) [ T₂ ] —→ t₁₂ [ X :τ= T₂ ]
  E-EqL : ∀ {t₁ t₂ t₁'}
    → t₁ —→ t₁'
    → t₁ === t₂ —→ t₁' === t₂
  E-EqR : ∀ {t₁ t₂ t₂'}
    → t₂ —→ t₂'
    → t₁ === t₂ —→ t₁ === t₂'
  E-EqTrue : ∀ {t₁ t₂}
    → (v₁ : Value t₁)
    → (v₂ : Value t₂)
    → V-Eq t₁ t₂
    → t₁ === t₂ —→ B′ true
  E-EqFalse : ∀ {t₁ t₂}
    → (v₁ : Value t₁)
    → (v₂ : Value t₂)
--  TODO: should a proof of inequality be passed here?
    → t₁ === t₂ —→ B′ false

-- -------------------------------------

-- -------------------------------------
-- CANONICAL FORMS

from-true-term : ∀ {S}
  → ∅ ⊢ B′ true ∶ S
  → ∅ ⊢ TTrue <: S
from-true-term T-True = S-Refl
from-true-term (T-Sub x y) = S-Trans (from-true-term x) y

from-false-term : ∀ {S}
  → ∅ ⊢ B′ false ∶ S
  → ∅ ⊢ TFalse <: S
from-false-term T-False = S-Refl
from-false-term (T-Sub x y) = S-Trans (from-false-term x) y

from-abs-term : ∀ {x t A B S}
  → ∅ ⊢ (ƛ x ∶ A ⋯> t ∶ B) ∶ S
  → (∃ λ B → ∅ ⊢ A ⇒ B <: S)
from-abs-term (T-Abs {T₂ = T₂} x) = (T₂ , S-Refl)
from-abs-term (T-Sub x y) with from-abs-term x
... | (B , z) = (B , S-Trans z y)

from-forall-term : ∀ {X A t S}
  → ∅ ⊢ Λ X <: A ⋯> t ∶ S
  → (∃ λ B → ∅ ⊢ (A X <: A ∶ B) <: S)
from-forall-term (T-TAbs {T₂ = T₂} x) = (T₂ , S-Refl)
from-forall-term (T-Sub x y) with from-forall-term x
... | (B , z) = (B , S-Trans z y)

-- impossible derivations

-- bool / forall

imp-true<:forall : ∀ {X T₁ T₂}
  → ∅ ⊢ TTrue <: A X <: T₁ ∶ T₂
  → ⊥
imp-true<:forall (S-Trans x y) with inversion-<:-forall y
... | inj₂ (a , b , refl) = imp-true<:forall x
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()

imp-false<:forall : ∀ {X T₁ T₂}
  → ∅ ⊢ TFalse <: A X <: T₁ ∶ T₂
  → ⊥
imp-false<:forall (S-Trans x y) with inversion-<:-forall y
... | inj₂ (a , b , refl) = imp-false<:forall x
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()

imp-bool:forall : ∀ {b X T₁ T₂}
  → ∅ ⊢ B′ b ∶ A X <: T₁ ∶ T₂
  → ⊥
imp-bool:forall {b = true} (T-Sub x y) = imp-true<:forall (S-Trans (from-true-term x) y)
imp-bool:forall {b = false} (T-Sub x y) = imp-false<:forall (S-Trans (from-false-term x) y)

-- abs / forall

imp-abs<:forall : ∀ {A B X T₁ T₂}
  → ∅ ⊢ A ⇒ B <: A X <: T₁ ∶ T₂
  → ⊥
imp-abs<:forall (S-Trans x y) with inversion-<:-forall y
... | inj₂ (a , b , refl) = imp-abs<:forall x
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()

imp-abs:forall : ∀ {x t A B X T₁ T₂}
  → ∅ ⊢ (ƛ x ∶ A ⋯> t ∶ B) ∶ (A X <: T₁ ∶ T₂)
  → ⊥
imp-abs:forall (T-Sub x y) with from-abs-term x
... | ( B , z ) = imp-abs<:forall (S-Trans z y)

-- abs / bool

imp-abs<:true : ∀ {A B}
  → ∅ ⊢ A ⇒ B <: TTrue
  → ⊥
imp-abs<:true (S-Trans x y) with inversion-<:-true y
... | inj₂ refl = imp-abs<:true x
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()

imp-abs<:false : ∀ {A B}
  → ∅ ⊢ A ⇒ B <: TFalse
  → ⊥
imp-abs<:false (S-Trans x y) with inversion-<:-false y
... | inj₂ refl = imp-abs<:false x
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()

imp-abs<:bool : ∀ {A B}
  → ∅ ⊢ A ⇒ B <: TBool
  → ⊥
imp-abs<:bool (S-Trans x y) with inversion-<:-bool y
... | inj₂ (inj₂ (inj₁ refl)) = imp-abs<:true x
... | inj₂ (inj₂ (inj₂ refl)) = imp-abs<:false x
... | inj₂ (inj₁ refl) = imp-abs<:bool x
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()

imp-abs:bool : ∀ {x t A B}
  → ∅ ⊢ (ƛ x ∶ A ⋯> t ∶ B) ∶ TBool
  → ⊥
imp-abs:bool (T-Sub x y) with from-abs-term x
... | ( B , z) = imp-abs<:bool (S-Trans z y)

-- forall / bool

imp-forall<:true : ∀ {X T₁ T₂}
  → ∅ ⊢ (A X <: T₁ ∶ T₂) <: TTrue
  → ⊥
imp-forall<:true (S-Trans x y) with inversion-<:-true y
... | inj₂ refl = imp-forall<:true x
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()

imp-forall<:false : ∀ {X T₁ T₂}
  → ∅ ⊢ (A X <: T₁ ∶ T₂) <: TFalse
  → ⊥
imp-forall<:false (S-Trans x y) with inversion-<:-false y
... | inj₂ refl = imp-forall<:false x
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()

imp-forall<:bool : ∀ {X T₁ T₂}
  → ∅ ⊢ A X <: T₁ ∶ T₂ <: TBool
  → ⊥
imp-forall<:bool (S-Trans x y) with inversion-<:-bool y
... | inj₂ (inj₂ (inj₁ refl)) = imp-forall<:true x
... | inj₂ (inj₂ (inj₂ refl)) = imp-forall<:false x
... | inj₂ (inj₁ refl) = imp-forall<:bool x
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()

imp-forall:bool : ∀ {X T₁ t}
  → ∅ ⊢  Λ X <: T₁ ⋯> t ∶ TBool
  → ⊥
imp-forall:bool (T-Sub x y) with from-forall-term x
... | (B , z) = imp-forall<:bool (S-Trans z y)

-- forall / abs

imp-forall<:abs : ∀ {X T₁ T₂ A B}
  → ∅ ⊢ A X <: T₁ ∶ T₂ <: A ⇒ B
  → ⊥
imp-forall<:abs (S-Trans x y) with inversion-<:-abs y
... | inj₂ (a , b , c , d , refl) = imp-forall<:abs x
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()

imp-forall:abs : ∀ {X T₁ t A B}
  → ∅ ⊢ Λ X <: T₁ ⋯> t ∶ A ⇒ B
  → ⊥
imp-forall:abs (T-Sub x y) with from-forall-term x
... | (B , z) = imp-forall<:abs (S-Trans z y)

-- bool / abs

imp-true<:abs : ∀ {A B}
  → ∅ ⊢ TTrue <: A ⇒ B
  → ⊥
imp-true<:abs (S-Trans x y) with inversion-<:-abs y
... | inj₂ (a , b , c , d , refl) = imp-true<:abs x
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()

imp-false<:abs : ∀ {A B}
  → ∅ ⊢ TFalse <: A ⇒ B
  → ⊥
imp-false<:abs (S-Trans x y) with inversion-<:-abs y
... | inj₂ (a , b , c , d , refl) = imp-false<:abs x
... | inj₁ (a , refl) with inversion-<:-var x
...   | ()

imp-bool:abs : ∀ {b A B}
  → ∅ ⊢ B′ b ∶ A ⇒ B
  → ⊥
imp-bool:abs {b = true} (T-Sub x y) = imp-true<:abs (S-Trans (from-true-term x) y)
imp-bool:abs {b = false} (T-Sub x y) = imp-false<:abs (S-Trans (from-false-term x) y)

-- canonical form lemmas

canonical-form-tabs : ∀ {v X T₁ T₂}
  → Value v
  → ∅ ⊢ v ∶ A X <: T₁ ∶ T₂
  → ∃ λ t₂ → v ≡ Λ X <: T₁ ⋯> t₂
canonical-form-tabs (V-Abs) (T-Sub x y) = ⊥-elim (imp-abs:forall (T-Sub x y))
canonical-form-tabs (V-Bool) (T-Sub x y) = ⊥-elim (imp-bool:forall (T-Sub x y))
canonical-form-tabs (V-TAbs {t = t}) (T-TAbs _) = (t , refl)
canonical-form-tabs (V-TAbs {t = t}) (T-Sub x y) with inversion-:-tabs x y
... | (S₂ , refl , refl , s₂:S₂ , S₂<:U) = (t , refl)

canonical-form-bool : ∀ {v}
  → Value v
  → ∅ ⊢ v ∶ TBool
  → ∃ λ b → v ≡ B′ b
canonical-form-bool (V-Abs) (T-Sub x y) = ⊥-elim (imp-abs:bool (T-Sub x y))
canonical-form-bool (V-Bool {b}) (T-Sub _ _) = (b , refl)
canonical-form-bool (V-TAbs) (T-Sub x y) = ⊥-elim (imp-forall:bool (T-Sub x y))

canonical-form-abs : ∀ {v A B}
  → Value v
  → ∅ ⊢ v ∶ A ⇒ B
  → ∃ λ x → ∃ λ t → ∃ λ S₁ → ∃ λ S₂ → v ≡ ƛ x ∶ S₁ ⋯> t ∶ S₂ × ∅ ⊢ A <: S₁
canonical-form-abs (V-Abs {x} {T₁} {T₂} {t}) (T-Abs a) = (x , t , T₁ , T₂ , refl , S-Refl)
canonical-form-abs (V-Abs {x} {T₁} {T₂} {t}) (T-Sub a b) with inversion-:-abs a b
... | (S₂ , c) = (x , t , T₁ , T₂ , refl , {!!})
canonical-form-abs V-Bool (T-Sub x y) = ⊥-elim (imp-bool:abs (T-Sub x y))
canonical-form-abs V-TAbs (T-Sub x y) = ⊥-elim (imp-forall:abs (T-Sub x y))

-- -------------------------------------

-- -------------------------------------
-- PROGRESS

data Progress (t : Term) : Set where
  step : ∀ {t'}
    → t —→ t'
    → Progress t
  done :
       Value t
    → Progress t

var-empty-ctx : ∀ {x T}
  → ∅ ⊢ ′ x ∶ T
  → ⊥
var-empty-ctx (T-Var ())
var-empty-ctx (T-Sub x y) = var-empty-ctx x

progress : ∀ {t T}
  → ∅ ⊢ t ∶ T
  → Progress t
progress (T-Var ())
progress (T-Abs d) = done V-Abs
progress (T-App ⊢t₁ ⊢t₂) with progress ⊢t₁
... | step t₁—→t₁' = step (E-App1 t₁—→t₁')
... | done v₁ with progress ⊢t₂
...   | step t₂—→t₂' = step (E-App2 t₂—→t₂')
...   | done v₂ with canonical-form-abs v₁ ⊢t₁
...     | (_ , _ , _ , _ , refl , _) = step (E-AppAbs)
progress (T-True) = done (V-Bool)
progress (T-False) = done (V-Bool)
progress (T-If ⊢t ⊢t₁ ⊢t₂) with progress ⊢t
... | step t—→t' = step (E-If t—→t')
... | done v with canonical-form-bool v ⊢t
...   | (true , refl) = step (E-IfTrue)
...   | (false , refl) = step (E-IfFalse)
progress (T-TAbs ⊢t₂) = done (V-TAbs)
progress (T-TApp {X = X} ⊢t₁ ⊢X<:) with progress ⊢t₁
... | step t₁—→t₁' = step (E-TApp t₁—→t₁')
... | done v₁ with canonical-form-tabs v₁ ⊢t₁
...   | (_ , refl) =  step (E-TAppAbs)
progress (T-Sub t:S S<:T) = progress t:S
progress (T-Eq t₁:T t₂:T) with progress t₁:T
... | step t₁—→t₁' = step (E-EqL t₁—→t₁')
... | done v₁ with progress t₂:T
...   | step t₂—→t₂' = step (E-EqR t₂—→t₂')
...   | done v₂ with v-eq v₁ v₂
...     | inj₁ eq-proof = step (E-EqTrue v₁ v₂ eq-proof)
...     | inj₂ _ = step (E-EqFalse v₁ v₂)
progress (T-IfTrueR x:X t₂:T t₃:T) = ⊥-elim (var-empty-ctx x:X)

-- -------------------------------------

-- -------------------------------------
-- SUBSTITUTION

postulate
  subst-preserves-typing : ∀ {Γ q Q x t T}
    → ∅ ⊢ q ∶ Q
    → Γ , x ∶ Q ⊢ t ∶ T
    → Γ ⊢ t [ x := q ] ∶ T

postulate
  type-subst-preserves-subtyping : ∀ {Γ P Q X S T}
    → ∅ ⊢ P <: Q
    → Γ , X <: Q ⊢ S <: T
    → Γ ⊢ S [ X τ= P ] <: T [ X τ= P ]

postulate
  type-subst-preserves-typing : ∀ {Γ P Q X t T}
    → ∅ ⊢ P <: Q
    → Γ , X <: Q ⊢ t ∶ T
    → Γ ⊢ t [ X :τ= P ] ∶ T [ X τ= P ]

postulate
  ext-subt-ctx : ∀ {Γ S A x T}
    → Γ ⊢ S <: A
    → Γ , x ∶ T ⊢ S <: A

-- -------------------------------------

-- -------------------------------------
-- PRESERVATION

preserve : ∀ {M N A}
  → ∅ ⊢ M ∶ A
  → M —→ N
  → ∅ ⊢ N ∶ A
preserve (T-Var _) ()
preserve (T-Abs ⊢N) ()
preserve (T-App ⊢L ⊢M) (E-App1 L—→L′) = T-App (preserve ⊢L L—→L′) ⊢M
preserve (T-App ⊢L ⊢M) (E-App2 M—→M′) = T-App ⊢L (preserve ⊢M M—→M′)
preserve (T-App (T-Abs ⊢N) ⊢V) (E-AppAbs) = subst-preserves-typing ⊢V ⊢N
preserve (T-App (T-Sub M:S S<:T₁₂⇒A) t₂:T₁₂) (E-AppAbs) with inversion-:-abs M:S S<:T₁₂⇒A
... | (T₁₂<:T₁₁ , S₂<:A , t₁₂:S₂) = let
    t₂:T₁₁ = T-Sub t₂:T₁₂ T₁₂<:T₁₁
    t₁₂:A = T-Sub t₁₂:S₂ (ext-subt-ctx S₂<:A)
  in subst-preserves-typing t₂:T₁₁ t₁₂:A
preserve (T-True) ()
preserve (T-False) ()
preserve (T-If ⊢L ⊢M ⊢N) E-IfTrue = ⊢M
preserve (T-If ⊢L ⊢M ⊢N) E-IfFalse = ⊢N
preserve (T-If ⊢L ⊢M ⊢N) (E-If t—→t') = T-If (preserve ⊢L t—→t') ⊢M ⊢N
preserve (T-TAbs ⊢L) ()
preserve (T-TApp ⊢L ⊢X<:) (E-TApp L—→L') = T-TApp (preserve ⊢L L—→L') ⊢X<:
preserve (T-TApp (T-TAbs ⊢N) ⊢X<:) E-TAppAbs = type-subst-preserves-typing ⊢X<: ⊢N
preserve (T-TApp (T-Sub M:S S<:AX<:T₁₁:T₁₂) T₂<:T₁) (E-TAppAbs) with inversion-:-tabs M:S S<:AX<:T₁₁:T₁₂
... | (S₂ , refl , refl , t₁₂:S₂ , S₂<:T₁₂) = let
      t₁₂:T₁₂ = T-Sub t₁₂:S₂ S₂<:T₁₂
    in type-subst-preserves-typing T₂<:T₁ t₁₂:T₁₂
preserve (T-Sub M:S S<:A) M—→N = T-Sub (preserve M:S M—→N) S<:A
preserve (T-Eq t₁:T t₂:T) (E-EqL t—→t') = T-Eq (preserve t₁:T t—→t') t₂:T
preserve (T-Eq t₁:T t₂:T) (E-EqR t—→t') = T-Eq t₁:T (preserve t₂:T t—→t')
preserve (T-Eq t₁:T t₂:T) (E-EqTrue v₁ v₂ _) =  T-Sub T-True S-UnionL
preserve (T-Eq t₁:T t₂:T) (E-EqFalse v₁ v₂) = T-Sub T-False S-UnionR
preserve (T-IfTrueR {x = x} x:X t₂:T t₃:T) (E-If (E-EqL ()))
preserve (T-IfTrueR {x = x} x:X t₂:T t₃:T) (E-If (E-EqR ()))
preserve (T-IfTrueR {x = x} x:X t₂:T t₃:T) (E-If (E-EqTrue () _ _))
preserve (T-IfTrueR {x = x} x:X t₂:T t₃:T) (E-If (E-EqFalse () _))

-- -------------------------------------

-- -------------------------------------
-- EXAMPLES

ex1 : Term
ex1 = Λ "X" <: TBool ⋯> ƛ "x" ∶ ′′"X" ⋯> if (′"x") then (B′ true) else (′"x") ∶ [T= TTrue ,F= TFalse ][ ′′"X" ]
-}

-- -------------------------------------

{-
symbols:
≟ = \?=
⊎ = \u+
₁ = \_1
₂ = \_2
′ = \'
→ = \r (or \rightarrow)
ƛ = \Gl-
∶ = \:
⇒ = \=>
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
∨ = \or
-}
