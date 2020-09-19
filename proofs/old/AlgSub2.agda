module AlgSub where

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

data _⊢>_<:_ : Context → Type → Type → Set where
  SA-Top : ∀ {Γ S}
    → Γ ⊢> S <: Top
  SA-ReflTrue : ∀ {Γ}
    → Γ ⊢> TTrue <: TTrue
  SA-ReflFalse : ∀ {Γ}
    → Γ ⊢> TFalse <: TFalse
  SA-ReflTVar : ∀ {Γ X}
    → Γ ⊢> ′′ X <: ′′ X
  SA-TransTVar : ∀ {Γ X U T}
    → X <: U ∈ Γ
    → Γ ⊢> U <: T
    → Γ ⊢> ′′ X <: T
  SA-Arrow : ∀ {Γ S₁ S₂ T₁ T₂}
    → Γ ⊢> T₁ <: S₁
    → Γ ⊢> S₂ <: T₂
    → Γ ⊢> S₁ ⇒ S₂ <: T₁ ⇒ T₂
  SA-All : ∀ {Γ X U₁ S₂ T₂}
    → Γ , X <: U₁ ⊢> S₂ <: T₂
    → Γ ⊢> (A X <: U₁ ∶ S₂) <: (A X <: U₁ ∶ T₂)
  SA-UnionL : ∀ {Γ L R T}
    → Γ ⊢> T <: L
    → Γ ⊢> T <: L ∨ R
  SA-UnionR : ∀ {Γ L R T}
    → Γ ⊢> T <: R
    → Γ ⊢> T <: L ∨ R
  SA-UnionM : ∀ {Γ L R T}
    → Γ ⊢> L <: T
    → Γ ⊢> R <: T
    → Γ ⊢> L ∨ R <: T
  SA-MapTrueL : ∀ {Γ T₁ T₂ A}
    → Γ ⊢> T₁ <: A
    → Γ ⊢> [T= T₁ ,F= T₂ ][ TTrue ] <: A
  SA-MapTrueR : ∀ {Γ T₁ T₂ A}
    → Γ ⊢> A <: T₁
    → Γ ⊢> A <: [T= T₁ ,F= T₂ ][ TTrue ]
  SA-MapFalseL : ∀ {Γ T₁ T₂ A}
    → Γ ⊢> T₂ <: A
    → Γ ⊢> [T= T₁ ,F= T₂ ][ TFalse ] <: A
  SA-MapFalseR : ∀ {Γ T₁ T₂ A}
    → Γ ⊢> A <: T₂
    → Γ ⊢> A <: [T= T₁ ,F= T₂ ][ TFalse ]
  SA-MapBoolL : ∀ {Γ T₁ T₂}
    → Γ ⊢> [T= T₁ ,F= T₂ ][ TBool ] <: T₁ ∨ T₂
  SA-Map : ∀ {Γ S T T₁ T₂}
    → Γ ⊢> S <: T
    → Γ ⊢> [T= T₁ ,F= T₂ ][ S ] <: [T= T₁ ,F= T₂ ][ T ]

refl-<: : ∀ {Γ X}
  → Γ ⊢> X <: X
refl-<: {X = TTrue} = SA-ReflTrue
refl-<: {X = TFalse} = SA-ReflFalse
refl-<: {X = X ⇒ X₁} = SA-Arrow refl-<: refl-<:
refl-<: {X = ′′ x} = SA-ReflTVar
refl-<: {X = A x <: X ∶ X₁} = SA-All refl-<:
refl-<: {X = Top} = SA-Top
refl-<: {X = X ∨ X₁} = SA-UnionM (SA-UnionL refl-<:) (SA-UnionR refl-<:)
refl-<: {X = [T= X ,F= X₁ ][ X₂ ]} = SA-Map refl-<:

trans-<: : ∀ {Γ A B C}
  → Γ ⊢> A <: B
  → Γ ⊢> B <: C
  → Γ ⊢> A <: C
trans-<: x SA-Top = SA-Top
trans-<: x SA-ReflTrue = x
trans-<: x SA-ReflFalse = x
trans-<: x SA-ReflTVar = x
trans-<: x (SA-MapTrueR y) = SA-MapTrueR (trans-<: x y)
trans-<: x (SA-MapFalseR y) = SA-MapFalseR (trans-<: x y)
trans-<: x (SA-UnionL y) = SA-UnionL (trans-<: x y)
trans-<: x (SA-UnionR y) = SA-UnionR (trans-<: x y)
trans-<: (SA-TransTVar a b) y = SA-TransTVar a (trans-<: b y)
trans-<: (SA-UnionM a b) y = SA-UnionM (trans-<: a y) (trans-<: b y)
trans-<: (SA-MapTrueL x) y = SA-MapTrueL (trans-<: x y)
trans-<: (SA-MapFalseL x) y = SA-MapFalseL (trans-<: x y)
trans-<: SA-ReflTVar y = y
trans-<: (SA-Arrow a b) (SA-Arrow c d) = SA-Arrow (trans-<: c a) (trans-<: b d)
trans-<: (SA-All x) (SA-All y) = SA-All (trans-<: x y)
trans-<: (SA-UnionL x) (SA-UnionM y z) = trans-<: x y
trans-<: (SA-UnionR x) (SA-UnionM y z) = trans-<: x z
trans-<: (SA-MapTrueR x) (SA-MapTrueL y) = trans-<: x y
trans-<: (SA-MapTrueR x) (SA-Map y) = {!!}
trans-<: (SA-MapFalseR x) y = {!!}
trans-<: SA-MapBoolL (SA-UnionM y z) = {!!}
trans-<: (SA-Map x) (SA-MapTrueL y) = ?
trans-<: (SA-Map x) (SA-MapFalseL y) = ?
trans-<: (SA-Map x) SA-MapBoolL = ?
trans-<: (SA-Map x) (SA-Map y) = ?

{-
trans-<: x SA-Top = SA-Top
trans-<: x SA-ReflTrue = x
trans-<: x SA-ReflFalse = x
trans-<: x SA-ReflTVar = x
trans-<: x (SA-TransTVar y z) = {!!}
-- trans-<: (SA-TransTVar a b) y = SA-TransTVar a (trans-<: b y)
trans-<: (SA-TransTVar a b) (SA-Arrow c d) = SA-TransTVar a (trans-<: b (SA-Arrow c d))
trans-<: (SA-Arrow a b) (SA-Arrow c d) = SA-Arrow (trans-<: c a) (trans-<: b d)
-- trans-<: (SA-UnionM a b) y = SA-UnionM (trans-<: a y) (trans-<: b y)
trans-<: (SA-UnionM a b) (SA-Arrow c d) = SA-UnionM (trans-<: a (SA-Arrow c d)) (trans-<: b (SA-Arrow c d))
-- trans-<: (SA-MapTrueL x) y = SA-MapTrueL (trans-<: x y)
trans-<: (SA-MapTrueL x) (SA-Arrow y z) = SA-MapTrueL (trans-<: x (SA-Arrow y z))
trans-<: (SA-MapFalseL x) (SA-Arrow y z) = SA-MapFalseL (trans-<: x (SA-Arrow y z))
trans-<: x (SA-All y) = {!!}
trans-<: x (SA-UnionL y) = SA-UnionL (trans-<: x y)
trans-<: x (SA-UnionR y) = SA-UnionR (trans-<: x y)
trans-<: (SA-TransTVar a b) (SA-UnionM c d) = SA-TransTVar a (trans-<: b (SA-UnionM c d))
trans-<: (SA-UnionL x) (SA-UnionM y z) = trans-<: x y
trans-<: (SA-UnionR x) (SA-UnionM y z) = trans-<: x z
trans-<: (SA-UnionM a b) (SA-UnionM c d) = SA-UnionM (trans-<: a (SA-UnionM c d)) (trans-<: b (SA-UnionM c d))
trans-<: (SA-MapTrueL x) (SA-UnionM y z) = SA-MapTrueL (trans-<: x (SA-UnionM y z))
trans-<: (SA-MapFalseL x) (SA-UnionM y z) = SA-MapFalseL (trans-<: x (SA-UnionM y z))
trans-<: SA-MapBoolL (SA-UnionM y z) = {!!}
trans-<: x (SA-MapTrueL y) = {!(trans-<: (SA-MapTrueL refl-<:) y)!}
trans-<: x (SA-MapTrueR y) = {!!}
trans-<: x (SA-MapFalseL y) = {!!}
trans-<: x (SA-MapFalseR y) = {!!}
trans-<: x SA-MapBoolL = {!!}
trans-<: x (SA-Map y) = {!!}
-}
