module Subtyping where

open import Context
open import Type

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
  SA-ReflTVar : ∀ {Γ n}
    → Γ ⊢> ′′ n <: ′′ n
  SA-TransTVar : ∀ {Γ U T}
    → <: U ∈ Γ
    → Γ ⊢> U <: T
    → Γ ⊢> ′′ 0 <: T
  SA-Arrow : ∀ {Γ S₁ S₂ T₁ T₂}
    → Γ ⊢> T₁ <: S₁
    → Γ ⊢> S₂ <: T₂
    → Γ ⊢> S₁ ⇒ S₂ <: T₁ ⇒ T₂
  SA-All : ∀ {Γ U₁ S₂ T₂}
    → Γ ▹<: U₁ ⊢> S₂ <: T₂
    → Γ ⊢> (A<: U₁ ∶ S₂) <: (A<: U₁ ∶ T₂)
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
