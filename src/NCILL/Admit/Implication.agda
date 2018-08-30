module NCILL.Admit.Implication where

open import Data.List
open import Data.Empty

open import ListExtras
open import AssocProofs

open import NCILL.Types
open import NCILL.Ctx
open import NCILL.Sequent
open import NCILL.ProofUtils
open import NCILL.Admit.Action

-- IMPLICATION
------------------------------------------------------------------------

admit-impl-L-after : ∀ Γ Ψ Φ Δ₁ Δ₂ A B C D →
  Action2
    Γ C
    Ψ A
    (Δ₁ ++ B ∷ Φ ++ C ∷ Δ₂) D
    (((Δ₁ ++ Ψ) ++ A ⊸ B ∷ Φ) ++ Γ ++ Δ₂) D
admit-impl-L-after Γ Ψ Φ Δ₁ Δ₂ A B C D =
  action₂ (Δ₁ ++ B ∷ Φ) obligation₁ λ e₁ e₂ →
    subst-Sqnt-Γ obligation₂
    (impl-L Δ₁ e₁
    (subst-Sqnt-Γ obligation₃ e₂))
  where
    obligation₁ :  Δ₁ ++ B ∷ Φ ++ C ∷ Δ₂ ≡ (Δ₁ ++ B ∷ Φ) ++ C ∷ Δ₂
    obligation₁ = xs++xs++xs≡[xs++xs]++xs Δ₁ (B ∷ Φ) (C ∷ Δ₂)

    obligation₂ : Δ₁ ++ Ψ ++ A ⊸ B ∷ Φ ++ Γ ++ Δ₂ ≡ ((Δ₁ ++ Ψ) ++ A ⊸ B ∷ Φ) ++ Γ ++ Δ₂
    obligation₂ = xs++xs++xs++xs≡[[xs++xs]++xs]++xs Δ₁ Ψ (A ⊸ B ∷ Φ) (Γ ++ Δ₂)

    obligation₃ : (Δ₁ ++ B ∷ Φ) ++ Γ ++ Δ₂ ≡ Δ₁ ++ B ∷ Φ ++ Γ ++ Δ₂
    obligation₃ = [xs++xs]++xs≡xs++xs++xs Δ₁ (B ∷ Φ) (Γ ++ Δ₂)

admit-impl-L-before : ∀ Γ Ψ Δ₂ Δ₁ Ω₁ Ω₂ A B C D
  → Ω₁ ++ Ψ ≡ Δ₁ ++ C ∷ Δ₂
  → Action2
    Γ C
    Ψ A
    (Ω₁ ++ B ∷ Ω₂) D
    (Δ₁ ++ Γ ++ Δ₂ ++ A ⊸ B ∷ Ω₂) D
admit-impl-L-before  Γ Ψ Δ₂ Δ₁ Ω₁ Ω₂ A B C D eq with find-cons Ω₁ Δ₁ eq
admit-impl-L-before Γ Ψ Δ₂ Δ₁ Ω₁ Ω₂ A B C D _ | in-first Φ refl refl =
  action₂ Δ₁ obligation₁ λ e₁ e₂ →
    subst-Sqnt-Γ obligation₂
    (impl-L (Δ₁ ++ Γ ++ Φ) e₁
    (subst-Sqnt-Γ obligation₃ e₂))
  where
    obligation₁ : (Δ₁ ++ C ∷ Φ) ++ B ∷ Ω₂ ≡ Δ₁ ++ C ∷ Φ ++ B ∷ Ω₂
    obligation₁ = [xs++xs]++xs≡xs++xs++xs Δ₁ (C ∷ Φ) (B ∷ Ω₂)

    obligation₂ : (Δ₁ ++ Γ ++ Φ) ++ Ψ ++ A ⊸ B ∷ Ω₂ ≡ Δ₁ ++ Γ ++ (Φ ++ Ψ) ++ A ⊸ B ∷ Ω₂
    obligation₂ = [xs++xs++xs]++xs++xs≡xs++xs++[xs++xs]++xs Δ₁ Γ Φ Ψ (A ⊸ B ∷ Ω₂)

    obligation₃ : Δ₁ ++ Γ ++ Φ ++ B ∷ Ω₂ ≡ (Δ₁ ++ Γ ++ Φ) ++ B ∷ Ω₂
    obligation₃ = xs++xs++xs++xs≡[xs++xs++xs]++xs Δ₁ Γ Φ (B ∷ Ω₂)

admit-impl-L-before Γ Ψ Δ₂ Δ₁ Ω₁ Ω₂ A B C D _ | in-second Φ refl refl =
  action₁ Φ refl λ e₁ e₂ →
    subst-Sqnt-Γ obligation₁
    (impl-L Ω₁ e₁ e₂)
  where
    obligation₁ : Ω₁ ++ (Φ ++ Γ ++ Δ₂) ++ A ⊸ B ∷ Ω₂ ≡ (Ω₁ ++ Φ) ++ Γ ++ Δ₂ ++ A ⊸ B ∷ Ω₂
    obligation₁ = xs++[xs++xs++xs]++xs≡[xs++xs]++xs++xs++xs Ω₁ Φ Γ Δ₂ (A ⊸ B ∷ Ω₂)

admit-impl-L : ∀ Γ Ψ Δ₁ Δ₂ Ω₁ Ω₂ A B C D
  → Ω₁ ++ Ψ ++ A ⊸ B ∷ Ω₂ ≡ Δ₁ ++ C ∷ Δ₂
  → (A ⊸ B ≡ C → ⊥)
  → Action2
    Γ C
    Ψ A
    (Ω₁ ++ B ∷ Ω₂) D
    (Δ₁ ++ Γ ++ Δ₂) D
admit-impl-L Γ Ψ Δ₁ Δ₂ Ω₁ Ω₂ A B C D eq _ with match-cons-2 Ω₁ Ψ Δ₁ eq
admit-impl-L Γ Ψ Δ₁ Δ₂ Ω₁ Ω₂ A B C D _ ineq | here refl eq refl with ineq eq
... | ()
admit-impl-L Γ Ψ Δ₁ Δ₂ Ω₁ Ω₂ A B C D _ _ | before Φ eq refl =
  admit-impl-L-before Γ Ψ Φ Δ₁ Ω₁ Ω₂ A B C D eq
admit-impl-L Γ Ψ Δ₁ Δ₂ Ω₁ Ω₂ A B C D _ _ | after Φ refl refl =
  admit-impl-L-after Γ Ψ Φ Ω₁ Δ₂ A B C D

-- REVERSE IMPLICATION
------------------------------------------------------------------------

admit-app-L-after : ∀ (Γ Ψ Δ₁ Δ₂ Ω₁ Ω₂ : Ctx ) → (D C A B : Ty)
  → Ψ ++ Ω₂ ≡ Δ₁ ++ D ∷ Δ₂
  → Action2
    Γ D
    Ψ A
    (Ω₁ ++ B ∷ Ω₂) C
    ((Ω₁ ++ A ⊸ʳ B ∷ Δ₁) ++ Γ ++ Δ₂) C
admit-app-L-after  _ Ψ Δ₁ _ _ _ _ _ _ _ eq with find-cons Ψ Δ₁ eq
admit-app-L-after Γ Ψ Δ₁ _ Ω₁ Ω₂ D C A B eq | in-first Φ refl refl =
  action₁ Δ₁ refl λ e₁ e₂ →
    subst-Sqnt-Γ obligation₁ (impl-Lʳ Ω₁ e₁ e₂)
  where
    obligation₁ : Ω₁ ++ A ⊸ʳ B ∷ (Δ₁ ++ Γ ++ Φ) ++ Ω₂ ≡ (Ω₁ ++ A ⊸ʳ B ∷ Δ₁) ++ Γ ++ Φ ++ Ω₂
    obligation₁ = list-solve {n = 6}
      (bla :++ bla :++ (bla :++ bla :++ bla) :++ bla :≡ (bla :++ bla :++ bla) :++ bla :++ bla :++ bla)
      Ω₁ [ A ⊸ʳ B ] Δ₁ Γ Φ Ω₂
admit-app-L-after Γ Ψ Δ₁ Δ₂ Ω₁ _ D C A B eq | in-second Φ refl refl =
  action₂ (Ω₁ ++ B ∷ Φ) obligation₁ λ e₁ e₂ →
    subst-Sqnt-Γ obligation₃ (impl-Lʳ Ω₁ e₁ (subst-Sqnt-Γ obligation₂ e₂))
  where
    obligation₁ : Ω₁ ++ B ∷ Φ ++ D ∷ Δ₂ ≡ (Ω₁ ++ B ∷ Φ) ++ D ∷ Δ₂
    obligation₁ = xs++xs++xs≡[xs++xs]++xs Ω₁ (B ∷ Φ) (D ∷ Δ₂)

    obligation₂ : (Ω₁ ++ B ∷ Φ) ++ Γ ++ Δ₂ ≡ Ω₁ ++ B ∷ Φ ++ Γ ++ Δ₂
    obligation₂ = [xs++xs]++xs++xs≡xs++xs++xs++xs Ω₁ (B ∷ Φ) Γ Δ₂

    obligation₃ : Ω₁ ++ A ⊸ʳ B ∷ Ψ ++ Φ ++ Γ ++ Δ₂ ≡ (Ω₁ ++ A ⊸ʳ B ∷ Ψ ++ Φ) ++ Γ ++ Δ₂
    obligation₃ = xs++xs++xs++xs≡[xs++xs++xs]++xs Ω₁ (A ⊸ʳ B ∷ Ψ) Φ (Γ ++ Δ₂)

admit-app-L-before : (Γ Ψ Ω Δ₁ Δ₂ : Ctx) (A B C D : Ty)
  → Action2
    Γ A
    Ψ C
    ((Δ₁ ++ A ∷ Ω) ++ D ∷ Δ₂) B
    (Δ₁ ++ Γ ++ Ω ++ C ⊸ʳ D ∷ Ψ ++ Δ₂) B
admit-app-L-before Γ Ψ Ω Δ₁ Δ₂ A B C D =
  action₂ Δ₁ obligation₁ λ e₁ e₂ →
    subst-Sqnt-Γ obligation₃
    (impl-Lʳ (Δ₁ ++ Γ ++ Ω) e₁
    (subst-Sqnt-Γ obligation₂ e₂))
  where
    obligation₁ : (Δ₁ ++ A ∷ Ω) ++ D ∷ Δ₂ ≡ Δ₁ ++ A ∷ Ω ++ D ∷ Δ₂
    obligation₁ = [xs++xs]++xs≡xs++xs++xs Δ₁ (A ∷ Ω) (D ∷ Δ₂)

    obligation₂ : Δ₁ ++ Γ ++ Ω ++ D ∷ Δ₂ ≡ (Δ₁ ++ Γ ++ Ω) ++ D ∷ Δ₂
    obligation₂ = xs++xs++xs++xs≡[xs++xs++xs]++xs Δ₁ Γ Ω (D ∷ Δ₂)

    obligation₃ : (Δ₁ ++ Γ ++ Ω) ++ C ⊸ʳ D ∷ Ψ ++ Δ₂ ≡ Δ₁ ++ Γ ++ Ω ++ C ⊸ʳ D ∷ Ψ ++ Δ₂
    obligation₃ = [xs++xs++xs]++xs≡xs++xs++xs++xs Δ₁ Γ Ω (C ⊸ʳ D ∷ Ψ ++ Δ₂)

admit-app-L : (Γ Ψ Δ₁ Δ₂ Ω₁ Ω₂ : Ctx) → (A B C D : Ty)
  → Ω₁ ++ A ⊸ʳ B ∷ Ψ ++ Ω₂ ≡ Δ₁ ++ D ∷ Δ₂
  → (A ⊸ʳ B ≡ D → ⊥)
  → Action2
    Γ D
    Ψ A
    (Ω₁ ++ B ∷ Ω₂) C
    (Δ₁ ++ Γ ++ Δ₂) C
admit-app-L _ _ Δ₁ _ Ω₁ _ _ _ _ _ eq _  with match-cons Ω₁ Δ₁ eq
admit-app-L _ _ _ _ _ _ _ _ _ _ _ ineq | here _ eq _ with ineq eq
... | ()
admit-app-L Γ Ψ Δ₁ _ _ Ω₂ A B C D _ _  | before Φ refl refl =
  admit-app-L-before Γ Ψ Φ Δ₁ Ω₂ D C A B
admit-app-L Γ Ψ _ Δ₂ Ω₁ Ω₂ A B C D _ _  | after Φ eq refl =
  admit-app-L-after Γ Ψ Φ Δ₂ Ω₁ Ω₂ D C A B eq
