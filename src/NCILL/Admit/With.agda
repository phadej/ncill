module NCILL.Admit.With where

open import Data.List
open import Data.Empty

open import ListExtras
open import AssocProofs

open import NCILL.Types
open import NCILL.Ctx
open import NCILL.Sequent
open import NCILL.ProofUtils
open import NCILL.Admit.Action

admit-with-L-before₁ : ∀ Γ Ψ Δ₁ Δ₂ A B C D → Action
  Γ C
  ((Δ₁ ++ C ∷ Ψ) ++ A ∷ Δ₂) D
  (Δ₁ ++ Γ ++ Ψ ++ A & B ∷ Δ₂) D
admit-with-L-before₁ Γ Ψ Δ₁ Δ₂ A B C D =
  action Δ₁ obligation₁ λ t → process t by
    Δ₁ ++ Γ ++ Ψ ++ A ∷ Δ₂       ⊢ D ≡Γ⟨ obligation₂ ⟩
    (Δ₁ ++ Γ ++ Ψ) ++ A ∷ Δ₂     ⊢ D $⟨ with-L₁ (Δ₁ ++ Γ ++ Ψ) ⟩
    (Δ₁ ++ Γ ++ Ψ) ++ A & B ∷ Δ₂ ⊢ D ≡Γ⟨ obligation₃ ⟩
    Δ₁ ++ Γ ++ Ψ ++ A & B ∷ Δ₂   ⊢ D ∎
  where
    obligation₁ : (Δ₁ ++ C ∷ Ψ) ++ A ∷ Δ₂ ≡ Δ₁ ++ C ∷ Ψ ++ A ∷ Δ₂
    obligation₁ = [xs++xs]++xs≡xs++xs++xs Δ₁ (C ∷ Ψ) (A ∷ Δ₂)

    obligation₂ : Δ₁ ++ Γ ++ Ψ ++ A ∷ Δ₂ ≡ (Δ₁ ++ Γ ++ Ψ) ++ A ∷ Δ₂
    obligation₂ = xs++xs++xs++xs≡[xs++xs++xs]++xs Δ₁ Γ Ψ (A ∷ Δ₂)

    obligation₃ : (Δ₁ ++ Γ ++ Ψ) ++ A & B ∷ Δ₂ ≡ Δ₁ ++ Γ ++ Ψ ++ A & B ∷ Δ₂
    obligation₃ = [xs++xs++xs]++xs≡xs++xs++xs++xs Δ₁ Γ Ψ (A & B ∷ Δ₂)
    
admit-with-L-after₁ : ∀ Γ Ψ Δ₁ Δ₂ A B C D → Action
  Γ C
  (Δ₁ ++ A ∷ Ψ ++ C ∷ Δ₂) D
  ((Δ₁ ++ A & B ∷ Ψ) ++ Γ ++ Δ₂) D
admit-with-L-after₁ Γ Ψ Δ₁ Δ₂ A B C D =
  action (Δ₁ ++ A ∷ Ψ) obligation₁ λ t → process t by
    (Δ₁ ++ A ∷ Ψ) ++ Γ ++ Δ₂     ⊢ D ≡Γ⟨ obligation₂ ⟩
     Δ₁ ++ A ∷ Ψ  ++ Γ ++ Δ₂     ⊢ D $⟨ with-L₁ Δ₁ ⟩
     Δ₁ ++ A & B ∷ Ψ  ++ Γ ++ Δ₂ ⊢ D ≡Γ⟨ obligation₃ ⟩
    (Δ₁ ++ A & B ∷ Ψ) ++ Γ ++ Δ₂ ⊢ D ∎
  where
    obligation₁ : Δ₁ ++ A ∷ Ψ ++ C ∷ Δ₂ ≡ (Δ₁ ++ A ∷ Ψ) ++ C ∷ Δ₂
    obligation₁ = xs++xs++xs≡[xs++xs]++xs Δ₁ (A ∷ Ψ) (C ∷ Δ₂)

    obligation₂ : (Δ₁ ++ A ∷ Ψ) ++ Γ ++ Δ₂ ≡ Δ₁ ++ A ∷ Ψ ++ Γ ++ Δ₂
    obligation₂ = [xs++xs]++xs≡xs++xs++xs Δ₁ (A ∷ Ψ) (Γ ++ Δ₂)

    obligation₃ : Δ₁ ++ A & B ∷ Ψ ++ Γ ++ Δ₂ ≡ (Δ₁ ++ A & B ∷ Ψ) ++ Γ ++ Δ₂
    obligation₃ = xs++xs++xs≡[xs++xs]++xs Δ₁ (A & B ∷ Ψ) (Γ ++ Δ₂)

admit-with-L₁ : ∀ Γ Δ₁ Δ₂ Ω₁ Ω₂ A B C D
  → Ω₁ ++ A & B ∷ Ω₂ ≡ Δ₁ ++ C ∷ Δ₂
  → (A & B ≡ C → ⊥)
  → Action
    Γ C
    (Ω₁ ++ A ∷ Ω₂) D
    (Δ₁ ++ Γ ++ Δ₂) D
admit-with-L₁ Γ Δ₁ Δ₂ Ω₁ Ω₂ A B C D eq ineq with match-cons Ω₁ Δ₁ eq
admit-with-L₁ Γ Δ₁ Δ₂ Ω₁ Ω₂ A B C D _ ineq | here refl eq refl with ineq eq
... | ()
admit-with-L₁ Γ Δ₁ Δ₂ Ω₁ Ω₂ A B C D eq ineq | before Ψ refl refl =
  admit-with-L-before₁ Γ Ψ Δ₁ Ω₂ _ _ C D
admit-with-L₁ Γ Δ₁ Δ₂ Ω₁ Ω₂ A B C D eq ineq | after Ψ refl refl =
  admit-with-L-after₁ Γ Ψ Ω₁ Δ₂ _ _ C D

admit-with-L-before₂ : ∀ Γ Ψ Δ₁ Δ₂ A B C D → Action
  Γ C
  ((Δ₁ ++ C ∷ Ψ) ++ B ∷ Δ₂) D
  (Δ₁ ++ Γ ++ Ψ ++ A & B ∷ Δ₂) D
admit-with-L-before₂ Γ Ψ Δ₁ Δ₂ A B C D =
  action Δ₁ obligation₁ λ t → process t by
    Δ₁ ++ Γ ++ Ψ ++ B ∷ Δ₂       ⊢ D ≡Γ⟨ obligation₂ ⟩
    (Δ₁ ++ Γ ++ Ψ) ++ B ∷ Δ₂     ⊢ D $⟨ with-L₂ (Δ₁ ++ Γ ++ Ψ) ⟩
    (Δ₁ ++ Γ ++ Ψ) ++ A & B ∷ Δ₂ ⊢ D ≡Γ⟨ obligation₃ ⟩
    Δ₁ ++ Γ ++ Ψ ++ A & B ∷ Δ₂   ⊢ D ∎
  where
    obligation₁ : (Δ₁ ++ C ∷ Ψ) ++ B ∷ Δ₂ ≡ Δ₁ ++ C ∷ Ψ ++ B ∷ Δ₂
    obligation₁ = [xs++xs]++xs≡xs++xs++xs Δ₁ (C ∷ Ψ) (B ∷ Δ₂)

    obligation₂ : Δ₁ ++ Γ ++ Ψ ++ B ∷ Δ₂ ≡ (Δ₁ ++ Γ ++ Ψ) ++ B ∷ Δ₂
    obligation₂ = xs++xs++xs++xs≡[xs++xs++xs]++xs Δ₁ Γ Ψ (B ∷ Δ₂)

    obligation₃ : (Δ₁ ++ Γ ++ Ψ) ++ A & B ∷ Δ₂ ≡ Δ₁ ++ Γ ++ Ψ ++ A & B ∷ Δ₂
    obligation₃ = [xs++xs++xs]++xs≡xs++xs++xs++xs Δ₁ Γ Ψ (A & B ∷ Δ₂)
    
admit-with-L-after₂ : ∀ Γ Ψ Δ₁ Δ₂ A B C D → Action
  Γ C
  (Δ₁ ++ B ∷ Ψ ++ C ∷ Δ₂) D
  ((Δ₁ ++ A & B ∷ Ψ) ++ Γ ++ Δ₂) D
admit-with-L-after₂ Γ Ψ Δ₁ Δ₂ A B C D =
  action (Δ₁ ++ B ∷ Ψ) obligation₁ λ t → process t by
    (Δ₁ ++ B ∷ Ψ) ++ Γ ++ Δ₂     ⊢ D ≡Γ⟨ obligation₂ ⟩
     Δ₁ ++ B ∷ Ψ  ++ Γ ++ Δ₂     ⊢ D $⟨ with-L₂ Δ₁ ⟩
     Δ₁ ++ A & B ∷ Ψ  ++ Γ ++ Δ₂ ⊢ D ≡Γ⟨ obligation₃ ⟩
    (Δ₁ ++ A & B ∷ Ψ) ++ Γ ++ Δ₂ ⊢ D ∎
  where
    obligation₁ : Δ₁ ++ B ∷ Ψ ++ C ∷ Δ₂ ≡ (Δ₁ ++ B ∷ Ψ) ++ C ∷ Δ₂
    obligation₁ = xs++xs++xs≡[xs++xs]++xs Δ₁ (B ∷ Ψ) (C ∷ Δ₂)

    obligation₂ : (Δ₁ ++ B ∷ Ψ) ++ Γ ++ Δ₂ ≡ Δ₁ ++ B ∷ Ψ ++ Γ ++ Δ₂
    obligation₂ = [xs++xs]++xs≡xs++xs++xs Δ₁ (B ∷ Ψ) (Γ ++ Δ₂)

    obligation₃ : Δ₁ ++ A & B ∷ Ψ ++ Γ ++ Δ₂ ≡ (Δ₁ ++ A & B ∷ Ψ) ++ Γ ++ Δ₂
    obligation₃ = xs++xs++xs≡[xs++xs]++xs Δ₁ (A & B ∷ Ψ) (Γ ++ Δ₂)

admit-with-L₂ : ∀ Γ Δ₁ Δ₂ Ω₁ Ω₂ A B C D
  → Ω₁ ++ A & B ∷ Ω₂ ≡ Δ₁ ++ C ∷ Δ₂
  → (A & B ≡ C → ⊥)
  → Action
    Γ C
    (Ω₁ ++ B ∷ Ω₂) D
    (Δ₁ ++ Γ ++ Δ₂) D
admit-with-L₂ Γ Δ₁ Δ₂ Ω₁ Ω₂ A B C D eq ineq with match-cons Ω₁ Δ₁ eq
admit-with-L₂ Γ Δ₁ Δ₂ Ω₁ Ω₂ A B C D _ ineq | here refl eq refl with ineq eq
... | ()
admit-with-L₂ Γ Δ₁ Δ₂ Ω₁ Ω₂ A B C D eq ineq | before Ψ refl refl =
  admit-with-L-before₂ Γ Ψ Δ₁ Ω₂ _ _ C D
admit-with-L₂ Γ Δ₁ Δ₂ Ω₁ Ω₂ A B C D eq ineq | after Ψ refl refl =
  admit-with-L-after₂ Γ Ψ Ω₁ Δ₂ _ _ C D
