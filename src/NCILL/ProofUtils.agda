module NCILL.ProofUtils where

open import Data.List

open import ListExtras
open import AssocProofs

open import NCILL.Types
open import NCILL.Ctx
open import NCILL.Sequent

-- Proof utilities
------------------------------------------------------------------------

-- We will need to subtitute contexts in terms often.
subst-Sqnt-Γ : ∀ {Γ Δ A}
   → Γ ≡ Δ
   → Sqnt Γ A
   → Sqnt Δ A
subst-Sqnt-Γ refl x = x

infix  3 _⊢_∎
infixr 2 _⊢_≡Γ⟨_⟩_ _⊢_$⟨_⟩_
infix  1 process_by_

data Sqnt-Rewrite Γ A Δ B : Set where
  rewrite-to : (Sqnt Γ A → Sqnt Δ B) → Sqnt-Rewrite Γ A Δ B

process_by_ : ∀ {Γ A Δ B} → Sqnt Γ A → Sqnt-Rewrite Γ A Δ B → Sqnt Δ B
process t by rewrite-to f = f t

_⊢_≡Γ⟨_⟩_ : (Γ : Ctx) → (A : Ty) → ∀ {Δ} → Γ ≡ Δ → ∀ {Ω B} → Sqnt-Rewrite Δ A Ω B → Sqnt-Rewrite Γ A Ω B
Γ ⊢ A ≡Γ⟨ refl ⟩ r = r

_⊢_$⟨_⟩_ : (Γ : Ctx) → (A : Ty) → ∀ {Δ B} → (Sqnt Γ A → Sqnt Δ B) → ∀ {Ω C} → Sqnt-Rewrite Δ B Ω C → Sqnt-Rewrite Γ A Ω C
Γ ⊢ A $⟨ f ⟩ rewrite-to g = rewrite-to (λ t → g (f t))

_⊢_∎ : (Γ : Ctx) → (A : Ty) → Sqnt-Rewrite Γ A Γ A
_⊢_∎ Γ A = rewrite-to (λ t → t)
