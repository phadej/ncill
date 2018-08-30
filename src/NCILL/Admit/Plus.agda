module NCILL.Admit.Plus where

open import Data.List
open import Data.Empty

open import ListExtras
open import AssocProofs

open import NCILL.Types
open import NCILL.Ctx
open import NCILL.Sequent
open import NCILL.ProofUtils
open import NCILL.Admit.Action

admit-plus-L-before : ∀ (Γ Ψ Δ₁ Δ₂ : Ctx) → (A B C D : Ty) →
  Action-both
    Γ C
    ((Δ₁ ++ C ∷ Ψ) ++ A ∷ Δ₂) D
    ((Δ₁ ++ C ∷ Ψ) ++ B ∷ Δ₂) D
    (Δ₁ ++ Γ ++ Ψ ++ (A ⊕ B) ∷ Δ₂) D
admit-plus-L-before Γ Ψ Δ₁ Δ₂ A B C D =
  action-both Δ₁ (obligation₃ A) Δ₁ (obligation₃ B) λ e₁ e₂ →
    subst-Sqnt-Γ obligation₁
    (plus-L (Δ₁ ++ Γ ++ Ψ)
      (subst-Sqnt-Γ (obligation₂ A) e₁)
      (subst-Sqnt-Γ (obligation₂ B) e₂))
  where
    obligation₁ : (Δ₁ ++ Γ ++ Ψ) ++ A ⊕ B ∷ Δ₂ ≡ Δ₁ ++ Γ ++ Ψ ++ A ⊕ B ∷ Δ₂
    obligation₁ = [xs++xs++xs]++xs≡xs++xs++xs++xs Δ₁ Γ Ψ (A ⊕ B ∷ Δ₂)

    obligation₂ : ∀ X → Δ₁ ++ Γ ++ Ψ ++ X ∷ Δ₂ ≡ (Δ₁ ++ Γ ++ Ψ) ++ X ∷ Δ₂
    obligation₂ X = xs++xs++xs++xs≡[xs++xs++xs]++xs Δ₁ Γ Ψ (X ∷ Δ₂)

    obligation₃ : ∀ X → (Δ₁ ++ C ∷ Ψ) ++ X ∷ Δ₂ ≡ Δ₁ ++ C ∷ Ψ ++ X ∷ Δ₂
    obligation₃ X = [xs++xs]++xs≡xs++xs++xs Δ₁ (C ∷ Ψ) (X ∷ Δ₂) 

admit-plus-L-after : ∀ (Γ Ψ Δ₁ Δ₂ : Ctx) → (A B C D : Ty) →
  Action-both
    Γ C
    (Δ₁ ++ A ∷ Ψ ++ C ∷ Δ₂) D
    (Δ₁ ++ B ∷ Ψ ++ C ∷ Δ₂) D
    ((Δ₁ ++ (A ⊕ B) ∷ Ψ) ++ Γ ++ Δ₂) D
admit-plus-L-after  Γ Ψ Δ₁ Δ₂ A B C D =
  action-both (Δ₁ ++ A ∷ Ψ) (obligation₁ A) (Δ₁ ++ B ∷ Ψ) (obligation₁ B) λ e₁ e₂ →
    subst-Sqnt-Γ obligation₂
    (plus-L Δ₁
      (subst-Sqnt-Γ (obligation₃ A) e₁ )
      (subst-Sqnt-Γ (obligation₃ B) e₂))
  where
    obligation₁ : ∀ X → Δ₁ ++ X ∷ Ψ ++ C ∷ Δ₂ ≡ (Δ₁ ++ X ∷ Ψ) ++ C ∷ Δ₂
    obligation₁ X = xs++xs++xs≡[xs++xs]++xs Δ₁ (X ∷ Ψ) (C ∷ Δ₂)

    obligation₂ : Δ₁ ++ (A ⊕ B) ∷ Ψ ++ Γ ++ Δ₂ ≡ (Δ₁ ++ (A ⊕ B) ∷ Ψ) ++ Γ ++ Δ₂
    obligation₂ = xs++xs++xs≡[xs++xs]++xs Δ₁ (A ⊕ B ∷ Ψ) (Γ ++ Δ₂)

    obligation₃ : ∀ X → (Δ₁ ++ X ∷ Ψ) ++ Γ ++ Δ₂ ≡ Δ₁ ++ X ∷ Ψ ++ Γ ++ Δ₂
    obligation₃ X = [xs++xs]++xs≡xs++xs++xs Δ₁ (X ∷ Ψ) (Γ ++ Δ₂) 

admit-plus-L : ∀ Γ Δ₁ Δ₂ Ω₁ Ω₂ A B C D
  → Ω₁ ++ (A ⊕ B) ∷ Ω₂ ≡ Δ₁ ++ C ∷ Δ₂
  → (A ⊕ B ≡ C → ⊥)
  → Action-both
    Γ C
    (Ω₁ ++ A ∷ Ω₂) D
    (Ω₁ ++ B ∷ Ω₂) D
    (Δ₁ ++ Γ ++ Δ₂) D
admit-plus-L Γ Δ₁ Δ₂ Ω₁ Ω₂ A B C D eq _ with match-cons Ω₁ Δ₁ eq
admit-plus-L _ _ _ _ _ _ _ _ _ _ ineq | here _ eq _ with ineq eq
... | ()
admit-plus-L Γ Δ₁ Δ₂ Ω₁ Ω₂ A B C D _ _ | before Ψ refl refl =
  admit-plus-L-before Γ Ψ Δ₁ Ω₂ A B C D
admit-plus-L Γ Δ₁ Δ₂ Ω₁ Ω₂ A B C D _ _ | after  Ψ refl refl =
  admit-plus-L-after Γ Ψ Ω₁ Δ₂ A B C D
