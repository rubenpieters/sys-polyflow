module Typing where

open import Type
open import Context
open import Subtyping

-- exposure

data _⊢>_↑_ : Context → Type → Type → Set where
  XA-Promote : ∀ {Γ n T T'}
    → X <: T ∈ Γ
    → Γ ⊢> T ↑ T'
    → Γ ⊢> ′′ n ↑ T'
  XA-Other : ∀ {Γ T n}
    → T ≢ ′′ n
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
  TA-Var : ∀ {Γ n T}
    → x ∶ T ∈ Γ
    → Γ ⊢> ′ n ∶ T
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
