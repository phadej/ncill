module NCILL.Admit.Times where

open import Data.List
open import Data.Empty

open import ListExtras
open import AssocProofs

open import NCILL.Types
open import NCILL.Ctx
open import NCILL.Sequent
open import NCILL.ProofUtils
open import NCILL.Admit.Action

admit-times-L-before : (Γ Ψ Δ₁ Δ₂ : Ctx) → (A B C D : Ty)
  → Action
    Γ C
    ((Δ₁ ++ C ∷ Ψ) ++ A ∷ B ∷ Δ₂) D
    (Δ₁ ++ Γ ++ Ψ ++ A ⊗ B ∷ Δ₂) D
admit-times-L-before Γ Ψ Δ₁ Δ₂ A B C D =
  action Δ₁ obligation₁ λ t → process t by
    Δ₁ ++ Γ ++ Ψ ++ A ∷ B ∷ Δ₂   ⊢ D ≡Γ⟨ obligation₂ ⟩
    (Δ₁ ++ Γ ++ Ψ) ++ A ∷ B ∷ Δ₂ ⊢ D $⟨ times-L (Δ₁ ++ Γ ++ Ψ) ⟩
    (Δ₁ ++ Γ ++ Ψ) ++ A ⊗ B ∷ Δ₂ ⊢ D ≡Γ⟨ obligation₃ ⟩
    Δ₁ ++ Γ ++ Ψ ++ A ⊗ B ∷ Δ₂   ⊢ D ∎
  where
    obligation₁ : (Δ₁ ++ C ∷ Ψ) ++ A ∷ B ∷ Δ₂ ≡ Δ₁ ++ C ∷ Ψ ++ A ∷ B ∷ Δ₂
    obligation₁ = [xs++xs]++xs≡xs++xs++xs Δ₁ (C ∷ Ψ) (A ∷ B ∷ Δ₂)

    obligation₂ : Δ₁ ++ Γ ++ Ψ ++ A ∷ B ∷ Δ₂ ≡ (Δ₁ ++ Γ ++ Ψ) ++ A ∷ B ∷ Δ₂
    obligation₂ = xs++xs++xs++xs≡[xs++xs++xs]++xs Δ₁ Γ Ψ (A ∷ B ∷ Δ₂)

    obligation₃ : (Δ₁ ++ Γ ++ Ψ) ++ A ⊗ B ∷ Δ₂ ≡ Δ₁ ++ Γ ++ Ψ ++ A ⊗ B ∷ Δ₂
    obligation₃ = [xs++xs++xs]++xs≡xs++xs++xs++xs Δ₁ Γ Ψ (A ⊗ B ∷ Δ₂)

admit-times-L-after : (Γ Ψ Δ₁ Δ₂ : Ctx) → (A B C D : Ty)
  → Action
    Γ C
    (Δ₁ ++ A ∷ B ∷ Ψ ++ C ∷ Δ₂) D
    ((Δ₁ ++ A ⊗ B ∷ Ψ) ++ Γ ++ Δ₂) D
admit-times-L-after Γ Ψ Δ₁ Δ₂ A B C D =
  action (Δ₁ ++ A ∷ B ∷ Ψ) obligation₁ λ t → process t by
    (Δ₁ ++ A ∷ B ∷ Ψ) ++ Γ ++ Δ₂ ⊢ D ≡Γ⟨ obligation₂ ⟩
     Δ₁ ++ A ∷ B ∷ Ψ  ++ Γ ++ Δ₂ ⊢ D $⟨ times-L Δ₁ ⟩
     Δ₁ ++ A ⊗ B ∷ Ψ  ++ Γ ++ Δ₂ ⊢ D ≡Γ⟨ obligation₃ ⟩
    (Δ₁ ++ A ⊗ B ∷ Ψ) ++ Γ ++ Δ₂ ⊢ D ∎
  where
    obligation₁ : Δ₁ ++ A ∷ B ∷ Ψ ++ C ∷ Δ₂ ≡ (Δ₁ ++ A ∷ B ∷ Ψ) ++ C ∷ Δ₂
    obligation₁ = xs++xs++xs≡[xs++xs]++xs Δ₁ (A ∷ B ∷ Ψ) (C ∷ Δ₂)

    obligation₂ : (Δ₁ ++ A ∷ B ∷ Ψ) ++ Γ ++ Δ₂ ≡ Δ₁ ++ A ∷ B ∷ Ψ ++ Γ ++ Δ₂
    obligation₂ = [xs++xs]++xs≡xs++xs++xs Δ₁ (A ∷ B ∷ Ψ) (Γ ++ Δ₂)

    obligation₃ : Δ₁ ++ A ⊗ B ∷ Ψ ++ Γ ++ Δ₂ ≡ (Δ₁ ++ A ⊗ B ∷ Ψ) ++ Γ ++ Δ₂
    obligation₃ = xs++xs++xs≡[xs++xs]++xs Δ₁ (A ⊗ B ∷ Ψ) (Γ ++ Δ₂)

admit-times-L : (Γ Δ₁ Δ₂ Ω₁ Ω₂ : Ctx) → (A B C D : Ty)
  → Ω₁ ++ A ⊗ B ∷ Ω₂ ≡ Δ₁ ++ C ∷ Δ₂
  → (A ⊗ B ≡ C → ⊥)
  → Action Γ C (Ω₁ ++ A ∷ B ∷ Ω₂) D (Δ₁ ++ Γ ++ Δ₂) D
admit-times-L _ Δ₁ _ Ω₁ _ _ _ _ _ eq _ with match-cons Ω₁ Δ₁ eq
admit-times-L _ _ _ _ _ _ _ _ _ _ ineq | here _ eq _ with ineq eq
... | ()
admit-times-L Γ Δ₁ _ _ Ω₂ A B C D _ _ | before Ψ refl refl =
  admit-times-L-before Γ Ψ Δ₁ Ω₂ A B C D
admit-times-L Γ _ Δ₂ Ω₁ _ A B C D _ _ | after Ψ refl refl =
  admit-times-L-after Γ Ψ Ω₁ Δ₂ A B C D
