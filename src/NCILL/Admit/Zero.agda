module NCILL.Admit.Zero where

open import Data.List
open import ListExtras
open import AssocProofs

open import NCILL.Types
open import NCILL.Ctx
open import NCILL.Sequent
open import NCILL.ProofUtils

absurd-T0 : (Γ Δ₁ Δ₂ : Ctx) → (C : Ty) → Sqnt Γ ♯0 → Sqnt (Δ₁ ++ Γ ++ Δ₂) C
absurd-T0 _ Δ₁ _ _ var = zero-L Δ₁

absurd-T0 _ Δ₁ Δ₂ C (impl-L {Ψ} Ω₁ {Ω₂} {A} {B} t₁ t₂) =
  process absurd-T0 (Ω₁ ++ B ∷ Ω₂) Δ₁ Δ₂ C t₂ by
    Δ₁ ++ (Ω₁ ++ B ∷ Ω₂) ++ Δ₂          ⊢ C ≡Γ⟨ obligation₂ ⟩
    (Δ₁ ++ Ω₁) ++ B ∷ Ω₂ ++ Δ₂          ⊢ C $⟨ impl-L (Δ₁ ++ Ω₁) t₁ ⟩
    (Δ₁ ++ Ω₁) ++ Ψ ++ A ⊸ B ∷ Ω₂ ++ Δ₂ ⊢ C ≡Γ⟨ obligation₁ ⟩
    Δ₁ ++ (Ω₁ ++ Ψ ++ A ⊸ B ∷ Ω₂) ++ Δ₂ ⊢ C ∎
  where
    obligation₁ : (Δ₁ ++ Ω₁) ++ Ψ ++ A ⊸ B ∷ Ω₂ ++ Δ₂ ≡ Δ₁ ++ (Ω₁ ++ Ψ ++ A ⊸ B ∷ Ω₂) ++ Δ₂
    obligation₁ = [xs++xs]++xs++xs++xs≡xs++[xs++xs++xs]++xs Δ₁ Ω₁ Ψ (A ⊸ B ∷ Ω₂) Δ₂

    obligation₂ : Δ₁ ++ (Ω₁ ++ B ∷ Ω₂) ++ Δ₂ ≡ (Δ₁ ++ Ω₁) ++ B ∷ Ω₂ ++ Δ₂
    obligation₂ = xs++[xs++xs]++xs≡[xs++xs]++xs++xs Δ₁ Ω₁ (B ∷ Ω₂) Δ₂

absurd-T0 _ Δ₁ Δ₂ C (impl-Lʳ {Ψ} Ω₁ {Ω₂} {A} {B} t₁ t₂) =
  process absurd-T0 (Ω₁ ++ B ∷ Ω₂) Δ₁ Δ₂ C t₂ by
    Δ₁ ++ (Ω₁ ++ B ∷ Ω₂) ++ Δ₂           ⊢ C ≡Γ⟨ obligation₂ ⟩
    (Δ₁ ++ Ω₁) ++ B ∷ Ω₂ ++ Δ₂           ⊢ C $⟨ impl-Lʳ (Δ₁ ++ Ω₁) t₁ ⟩
    (Δ₁ ++ Ω₁) ++ A ⊸ʳ B ∷ Ψ ++ Ω₂ ++ Δ₂ ⊢ C ≡Γ⟨ obligation₁ ⟩
    Δ₁ ++ (Ω₁ ++ A ⊸ʳ B ∷ Ψ ++ Ω₂) ++ Δ₂ ⊢ C ∎
  where
    obligation₁ : (Δ₁ ++ Ω₁) ++ A ⊸ʳ B ∷ Ψ ++ Ω₂ ++ Δ₂ ≡ Δ₁ ++ (Ω₁ ++ A ⊸ʳ B ∷ Ψ ++ Ω₂) ++ Δ₂
    obligation₁ = [xs++xs]++xs++xs++xs≡xs++[xs++xs++xs]++xs Δ₁ Ω₁ (A ⊸ʳ B ∷ Ψ) Ω₂ Δ₂

    obligation₂ : Δ₁ ++ (Ω₁ ++ B ∷ Ω₂) ++ Δ₂ ≡ (Δ₁ ++ Ω₁) ++ B ∷ Ω₂ ++ Δ₂
    obligation₂ = xs++[xs++xs]++xs≡[xs++xs]++xs++xs Δ₁ Ω₁ (B ∷ Ω₂) Δ₂

absurd-T0 _ Δ₁ Δ₂ C (times-L Ω₁ {Ω₂} {A} {B} x) =
  subst-Sqnt-Γ obligation₂
  (times-L (Δ₁ ++ Ω₁)
  (subst-Sqnt-Γ obligation₁
  (absurd-T0 (Ω₁ ++ A ∷ B ∷ Ω₂) Δ₁ Δ₂ C x)))
  where
    obligation₁ : Δ₁ ++ (Ω₁ ++ A ∷ B ∷ Ω₂) ++ Δ₂ ≡ (Δ₁ ++ Ω₁) ++ A ∷ B ∷ Ω₂ ++ Δ₂
    obligation₁ = xs++[xs++xs]++xs≡[xs++xs]++xs++xs Δ₁ Ω₁ (A ∷ B ∷ Ω₂) Δ₂

    obligation₂ : (Δ₁ ++ Ω₁) ++ A ⊗ B ∷ Ω₂ ++ Δ₂ ≡ Δ₁ ++ (Ω₁ ++ A ⊗ B ∷ Ω₂) ++ Δ₂
    obligation₂ = [xs++xs]++xs++xs≡xs++[xs++xs]++xs Δ₁ Ω₁ (A ⊗ B ∷ Ω₂) Δ₂

absurd-T0 _ Δ₁ Δ₂ C (plus-L Ω₁ {Ω₂} {A} {B} e₁ e₂) =
  subst-Sqnt-Γ obligation₁ (plus-L (Δ₁ ++ Ω₁)
    (subst-Sqnt-Γ (obligation₂ A) x₁)
    (subst-Sqnt-Γ (obligation₂ B) x₂))
  where
    obligation₁ : (Δ₁ ++ Ω₁) ++ A ⊕ B ∷ Ω₂ ++ Δ₂ ≡ Δ₁ ++ (Ω₁ ++ A ⊕ B ∷ Ω₂) ++ Δ₂
    obligation₁ = [xs++xs]++xs++xs≡xs++[xs++xs]++xs Δ₁ Ω₁ (A ⊕ B ∷ Ω₂) Δ₂

    obligation₂ : ∀ X → Δ₁ ++ (Ω₁ ++ X ∷ Ω₂) ++ Δ₂ ≡ (Δ₁ ++ Ω₁) ++ X ∷ Ω₂ ++ Δ₂
    obligation₂ X = xs++[xs++xs]++xs≡[xs++xs]++xs++xs Δ₁ Ω₁ (X ∷ Ω₂) Δ₂

    x₁ = absurd-T0 _ Δ₁ Δ₂ C e₁
    x₂ = absurd-T0 _ Δ₁ Δ₂ C e₂

absurd-T0 _ Δ₁ Δ₂ C (zero-L Ω₁ {Ω₂}) =
  subst-Sqnt-Γ obligation₁ (zero-L (Δ₁ ++ Ω₁))
  where
    obligation₁ : (Δ₁ ++ Ω₁) ++ ♯0 ∷ Ω₂ ++ Δ₂ ≡ Δ₁ ++ (Ω₁ ++ ♯0 ∷ Ω₂) ++ Δ₂
    obligation₁ = [xs++xs]++xs++xs≡xs++[xs++xs]++xs Δ₁ Ω₁ (♯0 ∷ Ω₂) Δ₂

absurd-T0 _ Δ₁ Δ₂ C (with-L₁ Ω₁ {Ω₂} {A} {B} e) =
  subst-Sqnt-Γ obligation₁
  (with-L₁ (Δ₁ ++ Ω₁)
  (subst-Sqnt-Γ obligation₂
  (absurd-T0 (Ω₁ ++ A ∷ Ω₂) Δ₁ Δ₂ C e)))
  where
    obligation₁ : (Δ₁ ++ Ω₁) ++ A & B ∷ Ω₂ ++ Δ₂ ≡ Δ₁ ++ (Ω₁ ++ A & B ∷ Ω₂) ++ Δ₂
    obligation₁ = [xs++xs]++xs++xs≡xs++[xs++xs]++xs Δ₁ Ω₁ (A & B ∷ Ω₂) Δ₂

    obligation₂ : Δ₁ ++ (Ω₁ ++ A ∷ Ω₂) ++ Δ₂ ≡ (Δ₁ ++ Ω₁) ++ A ∷ Ω₂ ++ Δ₂
    obligation₂ = xs++[xs++xs]++xs≡[xs++xs]++xs++xs Δ₁ Ω₁ (A ∷ Ω₂) Δ₂

absurd-T0 _ Δ₁ Δ₂ C (with-L₂ Ω₁ {Ω₂} {A} {B} e) =
  subst-Sqnt-Γ obligation₁
  (with-L₂ (Δ₁ ++ Ω₁)
  (subst-Sqnt-Γ obligation₂
  (absurd-T0 (Ω₁ ++ B ∷ Ω₂) Δ₁ Δ₂ C e)))
  where
    obligation₁ : (Δ₁ ++ Ω₁) ++ A & B ∷ Ω₂ ++ Δ₂ ≡ Δ₁ ++ (Ω₁ ++ A & B ∷ Ω₂) ++ Δ₂
    obligation₁ = [xs++xs]++xs++xs≡xs++[xs++xs]++xs Δ₁ Ω₁ (A & B ∷ Ω₂) Δ₂

    obligation₂ : Δ₁ ++ (Ω₁ ++ B ∷ Ω₂) ++ Δ₂ ≡ (Δ₁ ++ Ω₁) ++ B ∷ Ω₂ ++ Δ₂
    obligation₂ = xs++[xs++xs]++xs≡[xs++xs]++xs++xs Δ₁ Ω₁ (B ∷ Ω₂) Δ₂

absurd-T0 _ Δ₁ Δ₂ C (unit-L Ω₁ {Ω₂} t) =
  subst-Sqnt-Γ obligation₂
  (unit-L (Δ₁ ++ Ω₁)
  (subst-Sqnt-Γ obligation₁
  (absurd-T0 _ Δ₁ Δ₂ C t)))
  where
    obligation₁ : Δ₁ ++ (Ω₁ ++ Ω₂) ++ Δ₂ ≡ (Δ₁ ++ Ω₁) ++ Ω₂ ++ Δ₂
    obligation₁ = xs++[xs++xs]++xs≡[xs++xs]++xs++xs Δ₁ Ω₁ Ω₂ Δ₂

    obligation₂ : (Δ₁ ++ Ω₁) ++ ♯1 ∷ Ω₂ ++ Δ₂ ≡ Δ₁ ++ (Ω₁ ++ ♯1 ∷ Ω₂) ++ Δ₂
    obligation₂ = [xs++xs]++xs++xs≡xs++[xs++xs]++xs Δ₁ Ω₁ (♯1 ∷ Ω₂) Δ₂
