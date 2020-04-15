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

data EType : Set where
  Read : EType
  Write : EType

data _⊢>_<:[_]_ : Context → Type → EType → Type → Set
data _⊢_⇛[_]_ : Context → Type → EType → Type → Set

data _⊢>_<:[_]_ where
  SA-Top : ∀ {Γ S α}
    → Γ ⊢> S <:[ α ] Top
  SA-ReflTrue : ∀ {Γ α}
    → Γ ⊢> TTrue <:[ α ] TTrue
  SA-ReflFalse : ∀ {Γ α}
    → Γ ⊢> TFalse <:[ α ] TFalse
  SA-ReflTVar : ∀ {Γ X α}
    → Γ ⊢> ′′ X <:[ α ] ′′ X
  SA-TransTVar : ∀ {Γ X U T α}
    → X <: U ∈ Γ
    → Γ ⊢> U <:[ α ] T
    → Γ ⊢> ′′ X <:[ α ] T
  SA-Arrow : ∀ {Γ S₁ S₂ T₁ T₂ α}
    → Γ ⊢> T₁ <:[ α ] S₁
    → Γ ⊢> S₂ <:[ α ] T₂
    → Γ ⊢> S₁ ⇒ S₂ <:[ α ] T₁ ⇒ T₂
  SA-All : ∀ {Γ X U₁ S₂ T₂ α}
    → Γ , X <: U₁ ⊢> S₂ <:[ α ] T₂
    → Γ ⊢> (A X <: U₁ ∶ S₂) <:[ α ] (A X <: U₁ ∶ T₂)
  SA-UnionL : ∀ {Γ L R T α}
    → Γ ⊢> T <:[ α ] L
    → Γ ⊢> T <:[ α ] L ∨ R
  SA-UnionR : ∀ {Γ L R T α}
    → Γ ⊢> T <:[ α ] R
    → Γ ⊢> T <:[ α ] L ∨ R
  SA-UnionM : ∀ {Γ L R T α}
    → Γ ⊢> L <:[ α ] T
    → Γ ⊢> R <:[ α ] T
    → Γ ⊢> L ∨ R <:[ α ] T
  SA-TEvalRead : ∀ {Γ T₁ T₂ T X B}
    → Γ ⊢ [T= T₁ ,F= T₂ ][ T ] ⇛[ Read ] X
    → Γ ⊢> X <:[ Read ] B
    → Γ ⊢> [T= T₁ ,F= T₂ ][ T ] <:[ Read ] B
  SA-TEvalWrite : ∀ {Γ A X T₁ T₂ T}
    → Γ ⊢ [T= T₁ ,F= T₂ ][ T ] ⇛[ Write ] X
    → Γ ⊢> A <:[ Write ] X
    → Γ ⊢> A <:[ Write ] [T= T₁ ,F= T₂ ][ T ]
  SA-MapRefl : ∀ {Γ T₁ T₂ T α}
    → Γ ⊢> [T= T₁ ,F= T₂ ][ T ] <:[ α ] [T= T₁ ,F= T₂ ][ T ]

-- -------------------------------------
-- TYPE EVALUATION RELATION

data _⊢_⇛[_]_ where
  TE-MapTrue : ∀ {Γ T₁ T₂ α}
    → Γ ⊢ [T= T₁ ,F= T₂ ][ TTrue ] ⇛[ α ] T₁
  TE-MapFalse : ∀ {Γ T₁ T₂ α}
    → Γ ⊢ [T= T₁ ,F= T₂ ][ TFalse ] ⇛[ α ] T₂
  TE-MapBoolRead : ∀ {Γ T₁ T₂}
    → Γ ⊢ [T= T₁ ,F= T₂ ][ TBool ] ⇛[ Read ] T₁ ∨ T₂
  TE-MapWrite : ∀ {Γ T₁ T₂ A B X}
    → Γ ⊢> B <:[ Write ] A
    → Γ ⊢ [T= T₁ ,F= T₂ ][ B ] ⇛[ Write ] X
    → Γ ⊢ [T= T₁ ,F= T₂ ][ A ] ⇛[ Write ] X
  TE-MapRead : ∀ {Γ T₁ T₂ A B X}
    → Γ ⊢> A <:[ Read ] B
    → Γ ⊢ [T= T₁ ,F= T₂ ][ B ] ⇛[ Read ] X
    → Γ ⊢ [T= T₁ ,F= T₂ ][ A ] ⇛[ Read ] X


{-
  TE-MapRead : ∀ {Γ A B T₁ T₂}
    → Γ ⊢> A <: B
    → Γ ⊢ [T= T₁ ,F= T₂ ][ A ] ⇛[ Read ] [T= T₁ ,F= T₂ ][ B ]
  TE-MapWrite : ∀ {Γ A B T₁ T₂}
    → Γ ⊢> A <: B
    → Γ ⊢ [T= T₁ ,F= T₂ ][ B ] ⇛[ Write ] [T= T₁ ,F= T₂ ][ A ]
  TE-Trans : ∀ {Γ T₁ T₂ X Y Z A}
    → Γ ⊢ [T= T₁ ,F= T₂ ][ X ] ⇛[ A ] [T= T₁ ,F= T₂ ][ Y ]
    → Γ ⊢ [T= T₁ ,F= T₂ ][ Y ] ⇛[ A ] Z
    → Γ ⊢ [T= T₁ ,F= T₂ ][ X ] ⇛[ A ] Z
-}






refl-<: : ∀ {Γ X α}
  → Γ ⊢> X <:[ α ] X
refl-<: {X = TTrue} = SA-ReflTrue
refl-<: {X = TFalse} = SA-ReflFalse
refl-<: {X = X ⇒ X₁} = SA-Arrow refl-<: refl-<:
refl-<: {X = ′′ x} = SA-ReflTVar
refl-<: {X = A x <: X ∶ X₁} = SA-All refl-<:
refl-<: {X = Top} = SA-Top
refl-<: {X = X ∨ X₁} = SA-UnionM (SA-UnionL refl-<:) (SA-UnionR refl-<:)
refl-<: {X = [T= X ,F= X₁ ][ X₂ ]} = SA-MapRefl

trans-<: : ∀ {Γ A B C α}
  → Γ ⊢> A <:[ α ] B
  → Γ ⊢> B <:[ α ] C
  → Γ ⊢> A <:[ α ] C
trans-<: x SA-Top = SA-Top
trans-<: x SA-ReflTrue = x
trans-<: x SA-ReflFalse = x
trans-<: x SA-ReflTVar = x
trans-<: x SA-MapRefl = x
trans-<: x (SA-UnionL y) = SA-UnionL (trans-<: x y)
trans-<: x (SA-UnionR y) = SA-UnionR (trans-<: x y)
trans-<: SA-ReflTVar y = y
trans-<: SA-MapRefl y = y
trans-<: (SA-TransTVar a b) y = SA-TransTVar a (trans-<: b y)
trans-<: (SA-UnionM a b) y = SA-UnionM (trans-<: a y) (trans-<: b y)
trans-<: (SA-Arrow a b) (SA-Arrow c d) = SA-Arrow (trans-<: c a) (trans-<: b d)
trans-<: (SA-All x) (SA-All y) = SA-All (trans-<: x y)
trans-<: (SA-UnionL x) (SA-UnionM y z) = trans-<: x y
trans-<: (SA-UnionR x) (SA-UnionM y z) = trans-<: x z
trans-<: (SA-TEvalRead x y) z = SA-TEvalRead x (trans-<: y z)
trans-<: x (SA-TEvalWrite y z) = SA-TEvalWrite y (trans-<: x z)

