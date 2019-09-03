module Alg2 where

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

Id : Set
Id = String

Label : Set
Label = String

_≠_ : ∀ (x y : String) → x ≢ y
x ≠ y  with x ≟ y
...       | no  x≢y  =  x≢y
...       | yes _    =  ⊥-elim impossible
  where postulate impossible : ⊥

data Obj : Set
data Type : Set

infixr 5 _∶_,_

data Obj where
  𝓞 : Obj
  _∶_,_ : Id → Type → Obj → Obj

infix 40 ⟨_⟩
infixl 35 _[_]
infix 50 L'_
infixr 45 _∨_

data Type where
  number : Type
  boolean : Type
  L'_ : Label → Type
  ⟨_⟩ : Obj → Type
  _[_] : Type → Type → Type
  _∨_ : Type → Type → Type
  ′_ : Id → Type

type1 = ⟨ "t" ∶ number , "f" ∶ boolean , 𝓞 ⟩ [ ′ "X" ]
type2 = L' "t" ∨ L' "f"

data Context : Set where
  ∅ : Context

data _⊢_<:_ : Context → Type → Type → Set where
  S-Refl : ∀ {Γ S}
    → Γ ⊢ S <: S
  S-UnionL : ∀ {Γ T L R}
    → Γ ⊢ T <: L
    → Γ ⊢ T <: L ∨ R
  S-UnionR : ∀ {Γ T L R}
    → Γ ⊢ T <: R
    → Γ ⊢ T <: L ∨ R

-- Inhabitants

data _<has-inhabitant>_ : Type → Label → Set where
  HI-Refl : ∀ {l}
    → L' l <has-inhabitant> l
  HI-UnionL : ∀ {l L R}
    → L <has-inhabitant> l
    → (L ∨ R) <has-inhabitant> l
  HI-UnionR : ∀ {l L R}
    → R <has-inhabitant> l
    → (L ∨ R) <has-inhabitant> l

data _<has-other-inhabitants-than>_ : Type → Label → Set where
  HOI-Neq : ∀ {l₁ l₂}
    → l₁ ≢ l₂
    → L' l₁ <has-other-inhabitants-than> l₂

-- Function

data FunctionSig : Set where
  ReturnType : Type → FunctionSig
  _<:_,_ : Id → Type → FunctionSig → FunctionSig

fun1 = "X" <: type2 , ReturnType type1

-- Instantiation

data Instantiation : Set where
  𝓘 : Instantiation
  _↦_,_ : Id → Type → Instantiation → Instantiation

inst1 = "X" ↦ L' "f" , 𝓘

data _<instantiated-as>_<in>_ : Id → Type → Instantiation → Set where
  IA-Base : ∀ {X T inst}
    → X <instantiated-as> T <in> (X ↦ T , inst)
  IA-Skip : ∀ {X₁ X₂ T₁ T₂ inst}
    → X₁ ≢ X₂
    → X₁ <instantiated-as> T₁ <in> inst
    → X₁ <instantiated-as> T₁ <in> (X₂ ↦ T₂ , inst)

data _<valid-inst-for>_ : Instantiation → FunctionSig → Set where
  VI-Return : ∀ {T}
    → 𝓘 <valid-inst-for> ReturnType T
  VI-Inst : ∀ {Γ X S T inst fun}
    → Γ ⊢ S <: T
    → inst <valid-inst-for> fun
    → (X ↦ S , inst) <valid-inst-for> (X <: T , fun)

valid-inst1 : inst1 <valid-inst-for> fun1
valid-inst1 = VI-Inst {Γ = ∅} (S-UnionR S-Refl) VI-Return

applyInst : (inst : Instantiation) → (fun : FunctionSig) → inst <valid-inst-for> fun → Type
applyInst inst fun valid-inst = {!!}

-- Flow

data FlowExpr : Set where
  return : FlowExpr
  ifₗ_===_then_else_ : Id → Label → FlowExpr → FlowExpr → FlowExpr
  ifᵣ_===_then_else_ : Label → Id → FlowExpr → FlowExpr → FlowExpr

flowexpr1 = ifₗ "X" === "t" then return else return

data <possible-path-of>_<with>_ : FlowExpr → Instantiation → Set where
  BI-Return : ∀ {inst}
    → <possible-path-of> return <with> inst
  BI-LeftTrue : ∀ {id label e₁ e₂ inst T}
    → <possible-path-of> e₁ <with> inst
    → id <instantiated-as> T <in> inst
    → T <has-inhabitant> label
    → <possible-path-of> (ifₗ id === label then e₁ else e₂) <with> inst
  BI-LeftFalse : ∀ {id label e₁ e₂ inst T}
    → <possible-path-of> e₂ <with> inst
    → id <instantiated-as> T <in> inst
    → T <has-other-inhabitants-than> label
    → <possible-path-of> (ifₗ id === label then e₁ else e₂) <with> inst

possible-path1 : <possible-path-of> flowexpr1 <with> inst1
possible-path1 = BI-LeftFalse BI-Return IA-Base (HOI-Neq ("f" ≠ "t"))

narrowedType : (flow : FlowExpr) → (fun : FunctionSig) → (inst : Instantiation) → inst <valid-inst-for> fun → <possible-path-of> flow <with> inst → Type
narrowedType flow fun inst valid-inst path = {!!}

-- Theorem

theorem :
  (fun : FunctionSig) →
  (flow : FlowExpr) →
  (inst : Instantiation) →
  inst <valid-inst-for> fun →
  (path : <possible-path-of> flow <with> inst) →
  Bool
theorem fun flow inst valid-inst path = true

theorem1 = theorem fun1 flowexpr1 inst1 valid-inst1 possible-path1


