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
open import Data.List using (_∷_; [])
open import Level
open import Data.String.Properties
open import Map <-strictTotalOrder-≈

Id : Set
Id = String

Label : Set
Label = String

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
  Λ_<:_⇨_ : Id → Type → Type → Type

e1 = ⟨ "t" ∶ number , "f" ∶ boolean , 𝓞 ⟩ [ L' "t" ]
e2 = ⟨ "t" ∶ number , "f" ∶ boolean , 𝓞 ⟩ [ ′ "X" ]

infix 10 _<canindex>_

-- TODO
-- need to make a distinction between _<canlookup>_ which tells us that an index can be used to look up in an object, used in safeLookup
-- and _<canindex>_ which tells us that a type can be used to index another type, used in simplify for example, for this relation the context should be added

data _<canindex>_ : Type → Obj → Set where
  CI-Label : ∀ {l o t}
    → (L' l) <canindex> (l ∶ t , o)
  CI-Skip : ∀ {l₁ l₂ o t}
    → l₁ ≢ l₂
    → (L' l₁) <canindex> o
    → (L' l₁) <canindex> (l₂ ∶ t , o)

canIndex : (x : Type) → (o : Obj) → Dec (x <canindex> o)
canIndex number _ = no λ()
canIndex boolean _ = no λ()
canIndex (L' l) 𝓞 = no λ()
canIndex (L' l₁) (l₂ ∶ t , o) with l₁ ≟ l₂
... | yes refl = yes CI-Label
... | no l₁≠l₂ with canIndex (L' l₁) o
...   | yes canindex = yes (CI-Skip l₁≠l₂ canindex)
...   | no ¬canindex = no λ{CI-Label → l₁≠l₂ refl ; (CI-Skip _ x) → ¬canindex x}
canIndex ⟨ obj ⟩ _ = no λ()
canIndex (o [ i ]) _ = no λ()
canIndex (l ∨ r) _ = no λ()
canIndex (′ id) _ = no λ()
canIndex (Λ X <: T ⇨ U) _ = no λ()

safeLookup : (x : Type) → (o : Obj) → x <canindex> o → Type
safeLookup (L' _) (_ ∶ t , _) CI-Label = t
safeLookup (L' l) (_ ∶ _ , o) (CI-Skip _ canindex) = safeLookup (L' l) o canindex

data Context : Set where
  ∅ : Context

data _⊢_<:_ : Context → Type → Type → Set where
  S-Refl : ∀ {Γ S}
    → Γ ⊢ S <: S

data _⊢_⇝_ : Context → Type → Type → Set where
  TE-IndexedAccess : ∀ {Γ o i obj lᵢ}
    → Γ ⊢ o <: ⟨ obj ⟩
    → Γ ⊢ i <: lᵢ
    → (canindex : lᵢ <canindex> obj)
    → Γ ⊢ o [ i ] ⇝ safeLookup lᵢ obj canindex

simplify : (Γ : Context) → (T : Type) → Dec (∃[ T₂ ](Γ ⊢ T ⇝ T₂ ))
simplify Γ number = no λ()
simplify Γ boolean = no λ()
simplify Γ (L' l) = no λ()
simplify Γ ⟨ obj ⟩ = no λ()
simplify Γ (number [ i ]) = no λ{(_ , TE-IndexedAccess () _ _)}
simplify Γ (boolean [ i ]) = no λ{(_ , TE-IndexedAccess () _ _)}
simplify Γ ((L' l) [ i ]) = no λ{(_ , TE-IndexedAccess () _ _)}
simplify Γ (o [ i₁ ] [ i₂ ]) = no λ{(_ , TE-IndexedAccess () _ _)}
simplify Γ ((l ∨ r) [ i ]) = no λ{(_ , TE-IndexedAccess () _ _)}
simplify Γ ((′ id) [ i ]) = no λ{(_ , TE-IndexedAccess () _ _)}
simplify Γ ((Λ X <: T ⇨ U) [ i ]) = no λ{(_ , TE-IndexedAccess () _ _)}
simplify Γ (⟨ obj ⟩ [ i ]) with canIndex i obj
... | yes canindex = yes (safeLookup i obj canindex , TE-IndexedAccess S-Refl S-Refl canindex)
... | no ¬canindex = no λ{(_ , TE-IndexedAccess S-Refl S-Refl canindex) → ¬canindex canindex}
simplify Γ (l ∨ r) = no λ()
simplify Γ (′ id) = no λ()
simplify Γ (Λ X <: T ⇨ U) = no λ()

test = simplify ∅ e1

data FlowExpr : Set where
  return : FlowExpr
  ifₗ_===_then_else_ : Id → Label → FlowExpr → FlowExpr → FlowExpr
  ifᵣ_===_then_else_ : Label → Id → FlowExpr → FlowExpr → FlowExpr

data BranchType : Set where
  truebranch : BranchType
  falsebranch : BranchType

data Branch : Set where
  𝓑 : Branch
  _►_ : (Id × Label × BranchType) → Branch → Branch

b1 = ("X" , "t" , truebranch) ► 𝓑

data _<branchin>_ : Branch → FlowExpr → Set where
  BI-Empty : 𝓑 <branchin> return
  BI-LeftTrue : ∀ {id label b e₁ e₂}
    → b <branchin> e₁
    → ((id , label , truebranch) ► b) <branchin> (ifₗ id === label then e₁ else e₂)
  BI-LeftFalse : ∀ {id label b e₁ e₂}
    → b <branchin> e₂
    → ((id , label , falsebranch) ► b) <branchin> (ifₗ id === label then e₁ else e₂)
  BI-RightTrue : ∀ {id label b e₁ e₂}
    → b <branchin> e₁
    → ((id , label , truebranch) ► b) <branchin> (ifᵣ label === id then e₁ else e₂)
  BI-RightFalse : ∀ {id label b e₁ e₂}
    → b <branchin> e₂
    → ((id , label , falsebranch) ► b) <branchin> (ifᵣ label === id then e₁ else e₂)

data Function : Set where
  𝓕 : Function
  _<:_▻_ : Id → Type → Function → Function

f1 = "X" <: (L' "t") ▻ 𝓕

data Instantiation : Set where
  𝓘 : Instantiation
  _↦_,_ : Id → Type → Instantiation → Instantiation

i1 = "X" ↦ (L' "t") , 𝓘

-- TODO: context should also be part of this relation
data _<validinstfor>_ : Instantiation → Function → Set where
  VI-Empty : 𝓘 <validinstfor> 𝓕
  VI-Inst : ∀ {Γ X S T inst fun}
    → Γ ⊢ S <: T
    → inst <validinstfor> fun
    → (X ↦ S , inst) <validinstfor> (X <: T ▻ fun)

_[_↦_] : Type → Id → Type → Type
number [ X ↦ T ] = number
boolean [ X ↦ T ] = boolean
(L' l) [ X ↦ T ] = L' l
⟨ obj ⟩ [ X ↦ T ] = ⟨ substObj obj X T ⟩
  where
  substObj : Obj → Id → Type → Obj
  substObj 𝓞 _ _ = 𝓞
  substObj (l ∶ t , o) X T = (l ∶ (t [ X ↦ T ]) , substObj o X T)
(o [ i ]) [ X ↦ T ] = (o [ X ↦ T ]) [ (i [ X ↦ T ]) ]
(l ∨ r) [ X ↦ T ] = (l [ X ↦ T ]) ∨ (r [ X ↦ T ])
(Λ Y <: S ⇨ U) [ X ↦ T ] = Λ Y <: (S [ X ↦ T ]) ⇨ (U [ X ↦ T ])
(′ id) [ X ↦ T ] with id ≟ X
... | yes _ = T
... | no _ = ′ id

inst1 = e2 [ "X" ↦ L' "t" ]

-- TODO: prevent name capturing
-- can make a variant of subst function which takes the instantiation function
-- as opposed to doing each substitution separately
instantiate : Instantiation → Type → Type
instantiate 𝓘 T = T
instantiate (X ↦ Y , inst) T = instantiate inst (T [ X ↦ Y ])



{-



f1 : Type
f1 = ⟨ fromList (( "t" , number) ∷ ("f" , boolean) ∷ []) ⟩

f2 : Type
f2 = f1 [ L' "t" ]

data Sing {c : Level} {A : Set c} : A → Set c where
  sing : (x : A) -> Sing x

getSimplifiedIndexedAccessType : ∀ {objectType indexType}
  → (type : Sing (⟨ objectType ⟩ [ L' indexType ]))
  → Maybe Type
getSimplifiedIndexedAccessType (sing (⟨ objectType ⟩ [ L' indexType ])) = let
  resolved : Maybe Type
  resolved = lookup indexType objectType
  in resolved

test = getSimplifiedIndexedAccessType (sing f2)

-}


{-
symbols:
⟨ = \<
⟩ = \>
∅ = \emptyset
⊢ = \|-
⇝ = \squigarrowright
𝓞 = \MCO
𝓑 = \MCB
► = \t7
𝓕 = \MCF
▻ = \t8
-}
