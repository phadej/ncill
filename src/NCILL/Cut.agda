module NCILL.Cut where

open import Data.List as L

open import ListExtras
open import AssocProofs

open import NCILL.Admit
open import NCILL.Ctx
open import NCILL.ProofUtils
open import NCILL.Sequent
open import NCILL.SequentPlus
open import NCILL.Types

-- ADMISSIBLE CUT
------------------------------------------------------------------------

-- We can define cut for Sequents
cut : ∀ {Γ} → (Δ₁ : Ctx) → ∀ {Δ₂ A B}

  → Γ ⊢ A    → Δ₁ ++ A ∷ Δ₂ ⊢ B
---------------------------------
  → Δ₁ ++ Γ ++ Δ₂ ⊢ B

cut Δ₁ x y = admissibility-of-cut _ _ Δ₁ _ _ _ refl x y


cut-last : ∀ {Γ} → (Δ₁ : Ctx) → ∀ {A B}

  → Γ ⊢ A    → Δ₁ ++ [ A ] ⊢ B
--------------------------------
  → Δ₁ ++ Γ ⊢ B

cut-last Δ₁ x y = subst-Sqnt-Γ
  (list-solve
    (bla :++ bla :++ :[] :≡ bla :++ bla)
    Δ₁ _)
  (cut Δ₁ x y)

-- CUT ELIMINATION
------------------------------------------------------------------------

cut-elimination : ∀ {Γ A} → Sqnt⁺ Γ A → Sqnt Γ A
cut-elimination var⁺                = var
cut-elimination (cut⁺ Δ₁ t₁ t₂)     = cut Δ₁ (cut-elimination t₁) (cut-elimination t₂)
cut-elimination (impl-R⁺ e)         = impl-R (cut-elimination e)
cut-elimination (impl-L⁺ Δ₁ e e₁)   = impl-L Δ₁ (cut-elimination e) (cut-elimination e₁)
cut-elimination (impl-R⁺ʳ t)        = impl-Rʳ (cut-elimination t)
cut-elimination (impl-L⁺ʳ Δ₁ t₁ t₂) = impl-Lʳ Δ₁ (cut-elimination t₁) (cut-elimination t₂)
cut-elimination unit-R⁺             = unit-R
cut-elimination (unit-L⁺ Δ₁ t)      = unit-L Δ₁ (cut-elimination t)
cut-elimination top-R⁺              = top-R
cut-elimination (zero-L⁺ Δ₁)        = zero-L Δ₁
cut-elimination (times-R⁺ t₁ t₂)    = times-R (cut-elimination t₁) (cut-elimination t₂)
cut-elimination (times-L⁺ Δ₁ t)     = times-L Δ₁ (cut-elimination t)
cut-elimination (plus-R₁⁺ t)        = plus-R₁ (cut-elimination t)
cut-elimination (plus-R₂⁺ t)        = plus-R₂ (cut-elimination t)
cut-elimination (plus-L⁺ Δ₁ t₁ t₂)  = plus-L Δ₁ (cut-elimination t₁) (cut-elimination t₂)
cut-elimination (with-R⁺ e₁ e₂)     = with-R (cut-elimination e₁) (cut-elimination e₂)
cut-elimination (with-L₁⁺ Δ₁ e)     = with-L₁ Δ₁ (cut-elimination e)
cut-elimination (with-L₂⁺ Δ₁ e)     = with-L₂ Δ₁ (cut-elimination e)

-- COMPLETENESS
------------------------------------------------------------------------

completeness : ∀ {Γ A} → Sqnt Γ A → Sqnt⁺ Γ A
completeness var               = var⁺
completeness (impl-R e)        = impl-R⁺ (completeness e)
completeness (impl-L Δ₁ e e₁)  = impl-L⁺ Δ₁ (completeness e) (completeness e₁)
completeness (impl-Rʳ e)       = impl-R⁺ʳ (completeness e)
completeness (impl-Lʳ Δ₁ e e₁) = impl-L⁺ʳ Δ₁ (completeness e) (completeness e₁)
completeness (times-R e e₁)    = times-R⁺ (completeness e) (completeness e₁)
completeness (times-L Δ₁ e)    = times-L⁺ Δ₁ (completeness e)
completeness (plus-R₁ e)       = plus-R₁⁺ (completeness e)
completeness (plus-R₂ e)       = plus-R₂⁺ (completeness e)
completeness (plus-L Δ₁ e e₁)  = plus-L⁺ Δ₁ (completeness e) (completeness e₁)
completeness (with-R e e₁)     = with-R⁺ (completeness e) (completeness e₁)
completeness (with-L₁ Δ₁ e)    = with-L₁⁺ Δ₁ (completeness e)
completeness (with-L₂ Δ₁ e)    = with-L₂⁺ Δ₁ (completeness e)
completeness unit-R            = unit-R⁺
completeness (unit-L Δ₁ e)     = unit-L⁺ Δ₁ (completeness e)
completeness (zero-L Δ₁)       = zero-L⁺ Δ₁
completeness top-R             = top-R⁺
