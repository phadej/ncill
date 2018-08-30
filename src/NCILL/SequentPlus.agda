module NCILL.SequentPlus where

open import Data.List

open import NCILL.Types
open import NCILL.Ctx


-- SEQUENT WITH CUT
------------------------------------------------------------------------

data Sqnt⁺ : Ctx → Ty → Set where
  var⁺ : ∀ {A} → Sqnt⁺ [ A ] A

  cut⁺ : ∀ {Γ} → (Δ₁ : Ctx) → ∀ {Δ₂ A B}
    → Sqnt⁺ Γ A
    → Sqnt⁺ (Δ₁ ++ A ∷ Δ₂) B
    → Sqnt⁺ (Δ₁ ++ Γ ++ Δ₂) B

  impl-R⁺ : ∀ {Γ A B}
    → Sqnt⁺ (A ∷ Γ) B
    → Sqnt⁺ Γ (A ⊸ B)

  impl-L⁺ : ∀ {Γ} → (Δ₁ : Ctx) → ∀ {Δ₂ A B C}
    → Sqnt⁺ Γ A
    → Sqnt⁺ (Δ₁ ++ B ∷ Δ₂) C
    → Sqnt⁺ (Δ₁ ++ Γ ++ A ⊸ B ∷ Δ₂) C

  impl-R⁺ʳ : ∀ {Γ A B}
    → Sqnt⁺ (Γ ++ [ A ]) B
    → Sqnt⁺ Γ (A ⊸ʳ B)

  impl-L⁺ʳ : ∀ {Γ} → (Δ₁ : Ctx) → ∀ {Δ₂ A B C}
    → Sqnt⁺ Γ A
    → Sqnt⁺ (Δ₁ ++ B ∷ Δ₂) C
    → Sqnt⁺ (Δ₁ ++ A ⊸ʳ B ∷ Γ ++ Δ₂) C

  times-R⁺ : ∀ {Γ Δ A B}
    → Sqnt⁺ Γ A
    → Sqnt⁺ Δ B
    → Sqnt⁺ (Γ ++ Δ) (A ⊗ B)

  times-L⁺ : (Δ₁ : Ctx) → ∀ {Δ₂ A B C}
    → Sqnt⁺ (Δ₁ ++ A ∷ B ∷ Δ₂) C
    → Sqnt⁺ (Δ₁ ++ A ⊗ B ∷ Δ₂) C

  plus-R₁⁺ : ∀ {Γ A B}
    → Sqnt⁺ Γ A
    → Sqnt⁺ Γ (A ⊕ B)

  plus-R₂⁺ : ∀ {Γ A B}
    → Sqnt⁺ Γ B
    → Sqnt⁺ Γ (A ⊕ B)

  plus-L⁺ : (Δ₁ : Ctx) → ∀ {Δ₂ A B C}
    → Sqnt⁺ (Δ₁ ++ A ∷ Δ₂) C
    → Sqnt⁺ (Δ₁ ++ B ∷ Δ₂) C
    → Sqnt⁺ (Δ₁ ++ A ⊕ B ∷ Δ₂) C

  with-R⁺ : ∀ {Γ A B}
    → Sqnt⁺ Γ A
    → Sqnt⁺ Γ B
    → Sqnt⁺ Γ (A & B)

  with-L₁⁺ : (Δ₁ : Ctx) → ∀ {Δ₂ A B C}
    → Sqnt⁺ (Δ₁ ++ A ∷ Δ₂) C
    → Sqnt⁺ (Δ₁ ++ A & B ∷ Δ₂) C

  with-L₂⁺ : (Δ₁ : Ctx) → ∀ {Δ₂ A B C}
    → Sqnt⁺ (Δ₁ ++ B ∷ Δ₂) C
    → Sqnt⁺ (Δ₁ ++ A & B ∷ Δ₂) C

  unit-R⁺ : Sqnt⁺ [] ♯1

  unit-L⁺ : (Δ₁ : Ctx) → ∀ {Δ₂ A}
    → Sqnt⁺ (Δ₁ ++ Δ₂) A
    → Sqnt⁺ (Δ₁ ++ ♯1 ∷ Δ₂) A

  zero-L⁺ : (Δ₁ : Ctx) → ∀ {Δ₂ A}
    → Sqnt⁺ (Δ₁ ++ ♯0 ∷ Δ₂) A

  top-R⁺ : ∀ {Γ} → Sqnt⁺ Γ ♯⊤
