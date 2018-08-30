module NCILL.Admit.Action where

open import Data.List

open import ListExtras

open import NCILL.Types
open import NCILL.Ctx
open import NCILL.Sequent

data Action Γ A Δ B Ω C : Set where
  action
    : (Δ₁ : Ctx) → {Δ₂ : Ctx} → Δ ≡ Δ₁ ++ A ∷ Δ₂
    → ( Sqnt (Δ₁ ++ Γ ++ Δ₂) B
      → Sqnt Ω C
       )
    → Action Γ A Δ B Ω C

-- rename to Action-either
data Action2 Γ A Δ B Ω C Φ D : Set where
  action₁
    : (Δ₁ : Ctx) → {Δ₂ : Ctx} → Δ ≡ Δ₁ ++ A ∷ Δ₂
    → ( Sqnt (Δ₁ ++ Γ ++ Δ₂) B
      → Sqnt Ω C
      → Sqnt Φ D
      )
    → Action2 Γ A Δ B Ω C Φ D

  action₂
    : (Ω₁ : Ctx) → {Ω₂ : Ctx} → Ω ≡ Ω₁ ++ A ∷ Ω₂
    → ( Sqnt Δ B
      → Sqnt (Ω₁ ++ Γ ++ Ω₂) C
      → Sqnt Φ D
      )
    → Action2 Γ A Δ B Ω C Φ D

data Action-both Γ A Δ B Ω C Ψ D : Set where
  action-both
    : (Δ₁ : Ctx) → {Δ₂ : Ctx} → Δ ≡ Δ₁ ++ A ∷ Δ₂
    → (Ω₁ : Ctx) → {Ω₂ : Ctx} → Ω ≡ Ω₁ ++ A ∷ Ω₂
    → ( Sqnt (Δ₁ ++ Γ ++ Δ₂) B
      → Sqnt (Ω₁ ++ Γ ++ Ω₂) C
      → Sqnt Ψ D
      )
    → Action-both Γ A Δ B Ω C Ψ D
