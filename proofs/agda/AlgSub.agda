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

data _⊢>_<:_ : Context → Type → Type → Set
data _⊢_⇛[_]_ : Context → Type → EType → Type → Set

data _⊢>_<:_ where
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
  SA-TEvalRead : ∀ {Γ T₁ T₂ T X B}
    → Γ ⊢ [T= T₁ ,F= T₂ ][ T ] ⇛[ Read ] X
    → Γ ⊢> X <: B
    → Γ ⊢> [T= T₁ ,F= T₂ ][ T ] <: B
  SA-TEvalWrite : ∀ {Γ A X T₁ T₂ T}
    → Γ ⊢ [T= T₁ ,F= T₂ ][ T ] ⇛[ Write ] X
    → Γ ⊢> A <: X
    → Γ ⊢> A <: [T= T₁ ,F= T₂ ][ T ]
  SA-MapRefl : ∀ {Γ T₁ T₂ T}
    → Γ ⊢> [T= T₁ ,F= T₂ ][ T ] <: [T= T₁ ,F= T₂ ][ T ]

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
    → Γ ⊢> B <: A
    → Γ ⊢ [T= T₁ ,F= T₂ ][ B ] ⇛[ Write ] X
    → Γ ⊢ [T= T₁ ,F= T₂ ][ A ] ⇛[ Write ] X
  TE-MapRead : ∀ {Γ T₁ T₂ A B X}
    → Γ ⊢> A <: B
    → Γ ⊢ [T= T₁ ,F= T₂ ][ B ] ⇛[ Read ] X
    → Γ ⊢ [T= T₁ ,F= T₂ ][ A ] ⇛[ Read ] X

refl-<: : ∀ {Γ X}
  → Γ ⊢> X <: X
refl-<: {X = TTrue} = SA-ReflTrue
refl-<: {X = TFalse} = SA-ReflFalse
refl-<: {X = X ⇒ X₁} = SA-Arrow refl-<: refl-<:
refl-<: {X = ′′ x} = SA-ReflTVar
refl-<: {X = A x <: X ∶ X₁} = SA-All refl-<:
refl-<: {X = Top} = SA-Top
refl-<: {X = X ∨ X₁} = SA-UnionM (SA-UnionL refl-<:) (SA-UnionR refl-<:)
refl-<: {X = [T= X ,F= X₁ ][ X₂ ]} = SA-MapRefl

data _⊢_≅_ : Context → Type → Type → Set where
  Sim : ∀ {Γ A B}
    → Γ ⊢> A <: B
    → Γ ⊢> B <: A
    → Γ ⊢ A ≅ B

write-result : ∀ {Γ T₁ T₂ T X}
  → Γ ⊢ [T= T₁ ,F= T₂ ][ T ] ⇛[ Write ] X
  → (Γ ⊢> TTrue <: T × X ≡ T₁) ⊎ (Γ ⊢> TFalse <: T × X ≡ T₂)

read-result : ∀ {Γ T₁ T₂ T X}
  → Γ ⊢ [T= T₁ ,F= T₂ ][ T ] ⇛[ Read ] X
  → (Γ ⊢> T <: TTrue × X ≡ T₁) ⊎ (Γ ⊢> T <: TFalse × X ≡ T₂) ⊎ (Γ ⊢> T <: TBool × X ≡ T₁ ∨ T₂)

read-and-write : ∀ {Γ T₁ T₂ T A B}
  → Γ ⊢ [T= T₁ ,F= T₂ ][ T ] ⇛[ Write ] A
  → Γ ⊢ [T= T₁ ,F= T₂ ][ T ] ⇛[ Read ] B
  → Γ ⊢> A <: B

trans-<: : ∀ {Γ A B C}
  → Γ ⊢> A <: B
  → Γ ⊢> B <: C
  → Γ ⊢> A <: C

{-# TERMINATING #-}
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
trans-<: (SA-TEvalWrite a b) (SA-TEvalRead c d) = trans-<: b (trans-<: (read-and-write a c) d)

write-result TE-MapTrue = inj₁ (refl-<: , refl)
write-result TE-MapFalse = inj₂ (refl-<: , refl)
write-result (TE-MapWrite x y) with write-result y
... | inj₁ (a , refl) = inj₁ (trans-<: a x , refl)
... | inj₂ (a , refl) = inj₂ (trans-<: a x , refl)

read-result TE-MapTrue = inj₁ (refl-<: , refl)
read-result TE-MapFalse = inj₂ (inj₁ (refl-<: , refl))
read-result TE-MapBoolRead = inj₂ (inj₂ (refl-<: , refl))
read-result (TE-MapRead x y) with read-result y
... | inj₁ (a , refl) = inj₁ (trans-<: x a , refl)
... | inj₂ (inj₁ (a , refl)) = inj₂ (inj₁ (trans-<: x a , refl))
... | inj₂ (inj₂ (a , refl)) = inj₂ (inj₂ (trans-<: x a , refl))

read-and-write a b with (write-result a , read-result b)
... | inj₁ (x , refl) , inj₁ (y , refl) = refl-<:
... | inj₁ (x , refl) , inj₂ (inj₁ (y , refl)) = {!!} -- True < False: need well-formed contexts
... | inj₁ (x , refl) , inj₂ (inj₂ (y , refl)) = SA-UnionL refl-<:
... | inj₂ (x , refl) , inj₁ (y , refl) = {!!} -- False < True: need well-formed contexts
... | inj₂ (x , refl) , inj₂ (inj₁ (y , refl)) = refl-<:
... | inj₂ (x , refl) , inj₂ (inj₂ (y , refl)) = SA-UnionR refl-<:

{-
∅-inversion-true : ∀ {S}
  → ∅ ⊢> S <: TTrue → ∅ ⊢ S ≅ TTrue
∅-inversion-true SA-ReflTrue = Sim refl-<: refl-<:
∅-inversion-true (SA-UnionM x y) = Sim {!!} {!!}
-- only possible in a context where True<:T is present
∅-inversion-true (SA-TEvalRead x y) = Sim (SA-TEvalRead x y) (SA-TEvalWrite {!!} {!!})
-}

imp-⇒<:True : ∀ {Γ A B}
  → Γ ⊢> A ⇒ B <: TTrue
  → ⊥
imp-⇒<:True ()

imp-A<:True : ∀ {Γ X S T}
  → Γ ⊢> A X <: S ∶ T <: TTrue
  → ⊥
imp-A<:True ()

imp-A<:False : ∀ {Γ X S T}
  → Γ ⊢> A X <: S ∶ T <: TFalse
  → ⊥
imp-A<:False ()

-- -------------------------------------

-- -------------------------------------
-- TYPING RELATION

-- exposure

data _⊢>_↑_ : Context → Type → Type → Set where
  XA-Promote : ∀ {Γ X T T'}
    → X <: T ∈ Γ
    → Γ ⊢> T ↑ T'
    → Γ ⊢> ′′ X ↑ T'
  XA-Other : ∀ {Γ T X}
    → T ≢ ′′ X
    → Γ ⊢> T ↑ T

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
data _⊢>_∶_ : Context → Term → Type → Set where
  TA-Var : ∀ {Γ x T}
    → x ∶ T ∈ Γ
    → Γ ⊢> ′ x ∶ T
  TA-Abs : ∀ {Γ x t₂ T₁ T₂}
    → Γ , x ∶ T₁ ⊢> t₂ ∶ T₂
    -- t₂ ∶ T
    -- T <: T₂
    → Γ ⊢> (ƛ x ∶ T₁ ⋯> t₂ ∶ T₂) ∶ T₁ ⇒ T₂
  TA-App : ∀ {Γ t₁ t₂ T₁ T₂ A B X}
    → Γ ⊢> t₁ ∶ X
    → Γ ⊢> X <: T₁
    → Γ ⊢> T₁ ↑ A ⇒ B
    → Γ ⊢> t₂ ∶ T₂
    → Γ ⊢> T₂ <: A
    → Γ ⊢> t₁ ∙ t₂ ∶ B
  TA-True : ∀ {Γ}
    → Γ ⊢> B′ true ∶ TTrue
  TA-False : ∀ {Γ}
    → Γ ⊢> B′ false ∶ TFalse
  TA-If : ∀ {Γ A B t₁ t₂ t₃ T C}
    → Γ ⊢> t₁ ∶ T
    → Γ ⊢> T <: TBool
    → Γ ⊢> t₂ ∶ A
    → Γ ⊢> t₃ ∶ B
    → Γ ⊢> A <: C
    → Γ ⊢> B <: C
    → Γ ⊢> if t₁ then t₂ else t₃ ∶ C
  TA-IfTrueR : ∀ {Γ A B t₂ t₃ x X}
    → Γ ⊢> ′ x ∶ ′′ X
    → (Γ ,T<: X) ⊢> t₂ ∶ A
    → Γ ⊢> t₃ ∶ B
    → Γ ⊢> if (′ x === B′ true) then t₂ else t₃ ∶ A ∨ B
  TA-TAbs : ∀ {Γ X t₂ T₁ T₂}
    → Γ , X <: T₁ ⊢> t₂ ∶ T₂
    → Γ ⊢> Λ X <: T₁ ⋯> t₂ ∶ A X <: T₁ ∶ T₂
  TA-TApp : ∀ {Γ t₁ X T₁ T₁₁ T₁₂ T₂ S}
    → Γ ⊢> t₁ ∶ S
    → Γ ⊢> S <: T₁
    → Γ ⊢> T₁ ↑ (A X <: T₁₁ ∶ T₁₂)
    → Γ ⊢> T₂ <: T₁₁
    → Γ ⊢> t₁ [ T₂ ] ∶ T₁₂ [ X τ= T₂ ]
  TA-Eq : ∀ {Γ t₁ t₂ T₁ T₂}
    → Γ ⊢> t₁ ∶ T₁
    → Γ ⊢> t₂ ∶ T₂
    → Γ ⊢> t₁ === t₂ ∶ TBool


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

canonical-form-true : ∀ {Γ v}
  → Value v
  → Γ ⊢> v ∶ TTrue
  → v ≡ B′ true
canonical-form-true V-Bool TA-True = refl

canonical-form-bool<: : ∀ {Γ v T}
  → Value v
  → Γ ⊢> v ∶ T
  → Γ ⊢> T <: TBool
  → v ≡ B′ true ⊎ v ≡ B′ false
canonical-form-bool<: V-Abs (TA-Abs y) (SA-UnionL z) = ⊥-elim (imp-⇒<:True z)
canonical-form-bool<: V-Bool TA-True z = inj₁ refl
canonical-form-bool<: V-Bool TA-False z = inj₂ refl
canonical-form-bool<: V-TAbs (TA-TAbs y) (SA-UnionL z) = ⊥-elim (imp-A<:True z)
canonical-form-bool<: V-TAbs (TA-TAbs y) (SA-UnionR z) = ⊥-elim (imp-A<:False z)

canonical-form-abs : ∀ {Γ v A B T}
  → Value v
  → Γ ⊢> v ∶ T
  → Γ ⊢> T ↑ A ⇒ B
  → ∃ λ x → ∃ λ t → ∃ λ S₁ → ∃ λ S₂ → v ≡ ƛ x ∶ S₁ ⋯> t ∶ S₂ × ∅ ⊢> A <: S₁
canonical-form-abs (V-Abs {x} {T₁} {T₂} {t}) (TA-Abs _) (XA-Other _) = (x , t , T₁ , T₂ , refl , refl-<:)

canonical-form-abs2 : ∀ {Γ v A B T X}
  → Value v
  → Γ ⊢> v ∶ X
  → Γ ⊢> X <: T
  → Γ ⊢> T ↑ A ⇒ B
  → ∃ λ x → ∃ λ t → ∃ λ S₁ → ∃ λ S₂ → v ≡ ƛ x ∶ S₁ ⋯> t ∶ S₂ × Γ ⊢> A <: S₁
canonical-form-abs2 (V-Abs {x} {T₁} {T₂} {t}) (TA-Abs _) () (XA-Promote _ _)
canonical-form-abs2 (V-Abs {x} {T₁} {T₂} {t}) (TA-Abs _) (SA-Arrow z _) (XA-Other _) = (x , t , T₁ , T₂ , refl , z)

canonical-form-tabs : ∀ {Γ v X T T₁ T₂}
  → Value v
  → Γ ⊢> v ∶ T
  → Γ ⊢> T ↑ A X <: T₁ ∶ T₂
  → ∃ λ t₂ → v ≡ Λ X <: T₁ ⋯> t₂
canonical-form-tabs (V-TAbs {t = t}) (TA-TAbs _) (XA-Other _) = (t , refl)


canonical-form-tabs2 : ∀ {Γ v X T T₁ T₂ S}
  → Value v
  → Γ ⊢> v ∶ S
  → Γ ⊢> S <: T
  → Γ ⊢> T ↑ A X <: T₁ ∶ T₂
  → ∃ λ t₂ → v ≡ Λ X <: T₁ ⋯> t₂
canonical-form-tabs2 (V-TAbs {t = t}) (TA-TAbs _) () (XA-Promote _ _)
canonical-form-tabs2 (V-TAbs {t = t}) (TA-TAbs _) (SA-All z) (XA-Other _) = (t , refl)

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
  → ∅ ⊢> ′ x ∶ T
  → ⊥
var-empty-ctx (TA-Var ())

progress : ∀ {t T}
  → ∅ ⊢> t ∶ T
  → Progress t
progress (TA-Abs d) = done V-Abs
progress (TA-App ⊢t₁ x z ⊢t₂ y) with progress ⊢t₁
... | step t₁—→t₁' = step (E-App1 t₁—→t₁')
... | done v₁ with progress ⊢t₂
...   | step t₂—→t₂' = step (E-App2 t₂—→t₂')
...   | done v₂ with canonical-form-abs2 v₁ ⊢t₁ x z
...     | (_ , _ , _ , _ , refl , _) = step (E-AppAbs)
progress (TA-True) = done (V-Bool)
progress (TA-False) = done (V-Bool)
progress (TA-If ⊢t T<Bool ⊢t₁ ⊢t₂ y z) with progress ⊢t
... | step t—→t' = step (E-If t—→t')
... | done v with canonical-form-bool<: v ⊢t T<Bool
...   | inj₁ refl = step (E-IfTrue)
...   | inj₂ refl = step (E-IfFalse)
progress (TA-TAbs ⊢t₂) = done (V-TAbs)
progress (TA-TApp {X = X} ⊢t₁ x z ⊢X<:) with progress ⊢t₁
... | step t₁—→t₁' = step (E-TApp t₁—→t₁')
... | done v₁ with canonical-form-tabs2 v₁ ⊢t₁ x z
...   | (_ , refl) =  step (E-TAppAbs)
progress (TA-Eq t₁:T t₂:T) with progress t₁:T
... | step t₁—→t₁' = step (E-EqL t₁—→t₁')
... | done v₁ with progress t₂:T
...   | step t₂—→t₂' = step (E-EqR t₂—→t₂')
...   | done v₂ with v-eq v₁ v₂
...     | inj₁ eq-proof = step (E-EqTrue v₁ v₂ eq-proof)
...     | inj₂ _ = step (E-EqFalse v₁ v₂)
progress (TA-IfTrueR x:X t₂:T t₃:T) = ⊥-elim (var-empty-ctx x:X)

-- -------------------------------------

-- -------------------------------------
-- SUBSTITUTION

postulate
  subst-preserves-typing : ∀ {Γ q Q x t T}
    → ∅ ⊢> q ∶ Q
    → Γ , x ∶ Q ⊢> t ∶ T
    → Γ ⊢> t [ x := q ] ∶ T

{-
postulate
  subst-preserves-typing : ∀ {Γ q Q x t T}
    → ∅ ⊢> q ∶ X
    → ∅ ⊢> A ⇒ B ↑ C ⇒ D
    → ∅ , x ∶ A ⊢> t ∶ B
    → ∅ ⊢> X <: C
    → ∅ ⊢> t [ x := q ] ∶ T
-}

postulate
  type-subst-preserves-subtyping : ∀ {Γ P Q X S T}
    → ∅ ⊢> P <: Q
    → Γ , X <: Q ⊢> S <: T
    → Γ ⊢> S [ X τ= P ] <: T [ X τ= P ]

postulate
  type-subst-preserves-typing : ∀ {Γ P Q X t T}
    → ∅ ⊢> P <: Q
    → Γ , X <: Q ⊢> t ∶ T
    → Γ ⊢> t [ X :τ= P ] ∶ T [ X τ= P ]

postulate
  ext-subt-ctx : ∀ {Γ S A x T}
    → Γ ⊢> S <: A
    → Γ , x ∶ T ⊢> S <: A

-- -------------------------------------

-- -------------------------------------
-- PRESERVATION

preserve : ∀ {M N A}
  → ∅ ⊢> M ∶ A
  → M —→ N
  → ∃ λ B → ∅ ⊢> N ∶ B × ∅ ⊢> B <: A
preserve (TA-Var _) ()
preserve (TA-Abs ⊢N) ()
preserve {A = A} (TA-App ⊢L x z ⊢M y) (E-App1 L—→L′) with preserve ⊢L L—→L′
... | a , b , c = (A , TA-App b (trans-<: c x) z ⊢M y , refl-<:)
preserve {A = A} (TA-App ⊢L x z ⊢M y) (E-App2 M—→M′) with preserve ⊢M M—→M′
... | a , b , c = (A , TA-App ⊢L x z b (trans-<: c y) , refl-<:)
preserve (TA-App (TA-Abs x) z T₁⇒T₂↑A⇒B t₂∶T₂ T₂<A) (E-AppAbs) = {!!}
-- subst-preserves-typing ⊢V ⊢N
preserve (TA-True) ()
preserve (TA-False) ()
preserve (TA-If {A = A₁} ⊢L x ⊢M ⊢N y z) E-IfTrue = (A₁ , ⊢M , y)
preserve (TA-If {B = B} ⊢L x ⊢M ⊢N y z) E-IfFalse = (B , ⊢N , z)
preserve {A = A} (TA-If ⊢L x ⊢M ⊢N y z) (E-If t—→t') with preserve ⊢L t—→t'
... | a , b , c = (A , TA-If b (trans-<: c x) ⊢M ⊢N y z , refl-<:)
preserve (TA-TAbs ⊢L) ()
preserve {A = A} (TA-TApp ⊢L x z ⊢X<:) (E-TApp L—→L') with preserve ⊢L L—→L'
... | a , b , c = (A , TA-TApp b (trans-<: c x) z ⊢X<: , refl-<:)
preserve (TA-TApp (TA-TAbs ⊢N) x z ⊢X<:) E-TAppAbs = {!!}
-- type-subst-preserves-typing ⊢X<: ⊢N
preserve (TA-Eq t₁:T t₂:T) (E-EqL t—→t') with preserve t₁:T t—→t'
... | a , b , c = (TBool , TA-Eq b t₂:T , refl-<:)
preserve (TA-Eq t₁:T t₂:T) (E-EqR t—→t') with preserve t₂:T t—→t'
... | a , b , c = (TBool , TA-Eq t₁:T b , refl-<:)
preserve (TA-Eq t₁:T t₂:T) (E-EqTrue v₁ v₂ _) = (TTrue , TA-True , SA-UnionL refl-<:)
preserve (TA-Eq t₁:T t₂:T) (E-EqFalse v₁ v₂) = (TFalse , TA-False , SA-UnionR refl-<:)
preserve (TA-IfTrueR x:X t₂:T t₃:T) (E-If (E-EqL ()))
preserve (TA-IfTrueR x:X t₂:T t₃:T) (E-If (E-EqR ()))
preserve (TA-IfTrueR x:X t₂:T t₃:T) (E-If (E-EqTrue () _ _))
preserve (TA-IfTrueR x:X t₂:T t₃:T) (E-If (E-EqFalse () _))

-- -------------------------------------
