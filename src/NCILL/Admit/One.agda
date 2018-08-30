module NCILL.Admit.One where

open import Data.List
open import Data.Empty

open import ListExtras
open import AssocProofs

open import NCILL.Types
open import NCILL.Ctx
open import NCILL.Sequent
open import NCILL.ProofUtils

open import NCILL.Admit.Action

admit-unit-L-after : (Γ Ψ Δ₁ Δ₂ : Ctx) → (A B : Ty)
  → Action
    Γ A
    (Δ₁ ++ Ψ ++ A ∷ Δ₂) B
    ((Δ₁ ++ ♯1 ∷ Ψ) ++ Γ ++ Δ₂) B
admit-unit-L-after Γ Ψ Δ₁ Δ₂ A B =
  action (Δ₁ ++ Ψ) obligation₁ λ t → process t by
    (Δ₁ ++ Ψ) ++ Γ ++ Δ₂      ⊢ B ≡Γ⟨ obligation₂  ⟩
    Δ₁ ++ Ψ ++ Γ ++ Δ₂        ⊢ B $⟨ unit-L Δ₁ ⟩
    Δ₁ ++ ♯1 ∷ Ψ ++ Γ ++ Δ₂   ⊢ B ≡Γ⟨ obligation₃ ⟩
    (Δ₁ ++ ♯1 ∷ Ψ) ++ Γ ++ Δ₂ ⊢ B ∎
  where
    obligation₁ : Δ₁ ++ Ψ ++ A ∷ Δ₂ ≡ (Δ₁ ++ Ψ) ++ A ∷ Δ₂
    obligation₁ = xs++xs++xs≡[xs++xs]++xs Δ₁ Ψ (A ∷ Δ₂)

    obligation₂ : (Δ₁ ++ Ψ) ++ Γ ++ Δ₂ ≡ Δ₁ ++ Ψ ++ Γ ++ Δ₂
    obligation₂ = ++-assoc Δ₁ Ψ (Γ ++ Δ₂)

    obligation₃ : Δ₁ ++ ♯1 ∷ Ψ ++ Γ ++ Δ₂ ≡ (Δ₁ ++ ♯1 ∷ Ψ) ++ Γ ++ Δ₂
    obligation₃ = xs++xs++xs++xs≡[xs++xs]++xs++xs Δ₁ (♯1 ∷ Ψ) Γ Δ₂

admit-unit-L-before : (Γ Ψ Δ₁ Δ₂ : Ctx) → (A B : Ty)
  → Action
    Γ A
    ((Δ₁ ++ A ∷ Ψ) ++ Δ₂) B
    (Δ₁ ++ Γ ++ Ψ ++ ♯1 ∷ Δ₂) B
admit-unit-L-before Γ Ψ Δ₁ Δ₂ A B =
  action Δ₁ obligation₁ λ t →
    subst-Sqnt-Γ obligation₃
    (unit-L (Δ₁ ++ Γ ++ Ψ)
    (subst-Sqnt-Γ obligation₂ t))
  where
    obligation₁ : (Δ₁ ++ A ∷ Ψ) ++ Δ₂ ≡ Δ₁ ++ A ∷ Ψ ++ Δ₂
    obligation₁ = ++-assoc Δ₁ (A ∷ Ψ) Δ₂

    obligation₂ : Δ₁ ++ Γ ++ Ψ ++ Δ₂ ≡ (Δ₁ ++ Γ ++ Ψ) ++ Δ₂
    obligation₂ = xs++xs++xs++xs≡[xs++xs++xs]++xs Δ₁ Γ Ψ Δ₂

    obligation₃ : (Δ₁ ++ Γ ++ Ψ) ++ ♯1 ∷ Δ₂ ≡ Δ₁ ++ Γ ++ Ψ ++ ♯1 ∷ Δ₂
    obligation₃ = [xs++xs++xs]++xs≡xs++xs++xs++xs Δ₁ Γ Ψ (♯1 ∷ Δ₂)

admit-unit-L : (Γ Δ₁ Δ₂ Ω₁ Ω₂ : Ctx) → (A B : Ty)
    → Ω₁ ++ ♯1 ∷ Ω₂ ≡ Δ₁ ++ A ∷ Δ₂
    → (♯1 ≡ A → ⊥)
    → Action Γ A (Ω₁ ++ Ω₂) B (Δ₁ ++ Γ ++ Δ₂) B
admit-unit-L _ Δ₁ _ Ω₁ _ _ _ eq _ with match-cons Ω₁ Δ₁ eq
admit-unit-L _ _ _ _ _ _ _ _ ineq | here _ eq _ with ineq eq
... | ()
admit-unit-L Γ Δ₁ _ _ Ω₂ A B eq ineq | before ms refl refl =
  admit-unit-L-before Γ ms Δ₁ Ω₂ A B
admit-unit-L Γ _ Δ₂ Ω₁ _ A B eq ineq | after ms refl refl =
  admit-unit-L-after Γ ms Ω₁ Δ₂ A B
