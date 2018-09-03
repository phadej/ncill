module NCILL.Admit where

open import Data.List as L
open import Data.Product
open import Data.Empty

open import ListExtras
open import AssocProofs

open import NCILL.Types
open import NCILL.Ctx
open import NCILL.Sequent
open import NCILL.ProofUtils

open import NCILL.Admit.Action
open import NCILL.Admit.Implication
open import NCILL.Admit.Times
open import NCILL.Admit.Plus
open import NCILL.Admit.With
open import NCILL.Admit.Zero
open import NCILL.Admit.One

-- ADMISSIBILITY OF CUT
------------------------------------------------------------------------

admissibility-of-cut : (Γ Δ Δ₁ Δ₂ : Ctx) → (A B : Ty)
  → Δ ≡ Δ₁ ++ A ∷ Δ₂
  → Sqnt Γ A
  → Sqnt Δ B
  → Sqnt (Δ₁ ++ Γ ++ Δ₂) B

-- VARIABLES (ID)
------------------------------------------------------------------------

admissibility-of-cut _ Δ _ _ _ _ p var e = subst-Sqnt-Γ p e
admissibility-of-cut Γ _ Δ₁ _ _ _ p d var with singleton-lemma Δ₁ p
... | (refl , refl , refl) = subst-Sqnt-Γ (sym (++-id-right Γ)) d

-- LINEAR IMPLICATION
------------------------------------------------------------------------

admissibility-of-cut Γ _ Δ₁ Δ₂ X Y eq (impl-R d) (impl-L Ω₁ {Ω₂} {A} e)
  with match-cons-2 Ω₁ [ A ] Δ₁ {Ω₂} {Δ₂} eq
admissibility-of-cut Γ _ Δ₁ Δ₂ X Y _ (impl-R d) (impl-L Ω₁ {Ω₂} {A} {B} e) | here refl refl refl
  = subst-Sqnt-Γ obligation (admissibility-of-cut _ _ Ω₁ _ _ _ refl d e)
  where
    obligation : Ω₁ ++ ([ A ] ++ Γ) ++ Δ₂ ≡ (Ω₁ ++ [ A ]) ++ Γ ++ Δ₂
    obligation = xs++[xs++xs]++xs≡[xs++xs]++xs++xs Ω₁ [ A ] Γ Δ₂

admissibility-of-cut Γ _ Δ₁ Δ₂ X Y _  d@(impl-R _ ) (impl-L Ω₁ {Ω₂} {A} {B} e) | before Ψ eq refl = ?
{-
  with admit-impl-L-before Γ Ψ Φ Δ₁ Ω₁ Ω₂ _ _ _ _ eq
... | action₁ ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e₁) e₂
... | action₂ ctx ctx≡ f = f e₁ (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e₂)
-}

admissibility-of-cut Γ _ Δ₁ Δ₂ X Y eq d@(impl-R _) (impl-L Ω₁ {Ω₂} e) | after Ψ refl refl = ?
{-
  with admit-impl-L-after Γ Ψ Φ Ω₁ Δ₂ _ _ _ _
... | action₁ ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e₁) e₂
... | action₂ ctx ctx≡ f = f e₁ (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e₂)
-}

admissibility-of-cut Γ _ Δ₁ Δ₂ _ _ eq (impl-L Ω₁ {Ω₂} {A} {B} d ) e = {!!}
{-
  subst-Sqnt-Γ obligation₁
  (impl-L (Δ₁ ++ Ω₁) d₁
  (subst-Sqnt-Γ obligation₂
  (admissibility-of-cut _ _ Δ₁ _ _ _ eq d₂ e)))
  where
    obligation₁ : (Δ₁ ++ Ω₁) ++ Ψ ++ A ⊸ B ∷ Ω₂ ++ Δ₂ ≡ Δ₁ ++ (Ω₁ ++ Ψ ++ A ⊸ B ∷ Ω₂) ++ Δ₂
    obligation₁ = [xs++xs]++xs++xs++xs≡xs++[xs++xs++xs]++xs Δ₁ Ω₁ Ψ (A ⊸ B ∷ Ω₂) Δ₂

    obligation₂ : Δ₁ ++ (Ω₁ ++ B ∷ Ω₂) ++ Δ₂ ≡ (Δ₁ ++ Ω₁) ++ B ∷ Ω₂ ++ Δ₂
    obligation₂ = xs++[xs++xs]++xs≡[xs++xs]++xs++xs Δ₁ Ω₁ (B ∷ Ω₂) Δ₂
-}
admissibility-of-cut Γ _ Δ₁ Δ₂ _ _ refl d (impl-R e)
  = impl-R (admissibility-of-cut _ _ (_ ∷ Δ₁) _ _ _ refl d e)

{-
admissibility-of-cut Γ _ Δ₁ Δ₂ X Y eq d@(impl-Rʳ _)   (impl-L {Ψ} Ω₁ {Ω₂} e₁ e₂)
  with admit-impl-L Γ Ψ Δ₁ Δ₂ Ω₁ Ω₂ _ _ _ Y eq (λ ())
... | action₁ ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e₁) e₂
... | action₂ ctx ctx≡ f = f e₁ (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e₂)
admissibility-of-cut Γ _ Δ₁ Δ₂ X Y eq d@(times-R _ _) (impl-L {Ψ} Ω₁ {Ω₂} e₁ e₂)
  with admit-impl-L Γ Ψ Δ₁ Δ₂ Ω₁ Ω₂ _ _ _ Y eq (λ ())
... | action₁ ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e₁) e₂
... | action₂ ctx ctx≡ f = f e₁ (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e₂)
admissibility-of-cut Γ _ Δ₁ Δ₂ X Y eq d@(plus-R₁ _)   (impl-L {Ψ} Ω₁ {Ω₂} e₁ e₂)
  with admit-impl-L Γ Ψ Δ₁ Δ₂ Ω₁ Ω₂ _ _ _ Y eq (λ ())
... | action₁ ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e₁) e₂
... | action₂ ctx ctx≡ f = f e₁ (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e₂)
admissibility-of-cut Γ _ Δ₁ Δ₂ X Y eq d@(plus-R₂ _)   (impl-L {Ψ} Ω₁ {Ω₂} e₁ e₂)
  with admit-impl-L Γ Ψ Δ₁ Δ₂ Ω₁ Ω₂ _ _ _ Y eq (λ ())
... | action₁ ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e₁) e₂
... | action₂ ctx ctx≡ f = f e₁ (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e₂)
admissibility-of-cut Γ _ Δ₁ Δ₂ X Y eq d@(with-R _ _)  (impl-L {Ψ} Ω₁ {Ω₂} e₁ e₂)
  with admit-impl-L Γ Ψ Δ₁ Δ₂ Ω₁ Ω₂ _ _ _ Y eq (λ ())
... | action₁ ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e₁) e₂
... | action₂ ctx ctx≡ f = f e₁ (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e₂)
admissibility-of-cut Γ _ Δ₁ Δ₂ X Y eq d@unit-R        (impl-L {Ψ} Ω₁ {Ω₂} e₁ e₂)
  with admit-impl-L Γ Ψ Δ₁ Δ₂ Ω₁ Ω₂ _ _ _ Y eq (λ ())
... | action₁ ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e₁) e₂
... | action₂ ctx ctx≡ f = f e₁ (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e₂)
admissibility-of-cut Γ _ Δ₁ Δ₂ X Y eq d@top-R         (impl-L {Ψ} Ω₁ {Ω₂} e₁ e₂)
  with admit-impl-L Γ Ψ Δ₁ Δ₂ Ω₁ Ω₂ _ _ _ Y eq (λ ())
... | action₁ ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e₁) e₂
... | action₂ ctx ctx≡ f = f e₁ (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e₂)
-}

-- REVERSE LINEAR IMPLICATION
------------------------------------------------------------------------

admissibility-of-cut Γ _ Δ₁ Δ₂ a b p (impl-Rʳ d) (impl-Lʳ Ω₁ {Ω₂} {C} {D} e) = {!!} {- with match-cons Ω₁ Δ₁ p
... | here refl refl refl = subst-Sqnt-Γ obligation e
  where
    d′ : Sqnt (Γ ++ Ψ ++ []) D
    d′ = admissibility-of-cut _ _ Γ _ _ _ refl e₁ d

    e : Sqnt (Ω₁ ++ (Γ ++ Ψ ++ []) ++ Ω₂) b
    e = admissibility-of-cut _ _ Ω₁ _ _ _ refl d′ e₂

    obligation : Ω₁ ++ (Γ ++ Ψ ++ []) ++ Ω₂ ≡ Ω₁ ++ Γ ++ Ψ ++ Ω₂
    obligation = list-solve
      (bla :++ (bla :++ bla :++ :[]) :++ bla :≡ bla :++ bla :++ bla :++ bla)
      Ω₁ Γ Ψ Ω₂

admissibility-of-cut Γ _ Δ₁ Δ₂ X Y _ d@(impl-Rʳ _) (impl-Lʳ {Ψ} Ω₁ {Ω₂} {A} {B} e₁ e₂) | after Φ q refl = ?
{-
  with admit-app-L-after Γ Ψ Φ Δ₂ Ω₁ Ω₂ X Y A B q
... | action₁ ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e₁) e₂
... | action₂ ctx ctx≡ f = f e₁ (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e₂)
-}
admissibility-of-cut Γ _ Δ₁ Δ₂ X Y _ d@(impl-Rʳ _) (impl-Lʳ {Ψ} Ω₁ {Ω₂} {A} {B} e₁ e₂) | before Φ refl refl = ?
{-
  with admit-app-L-before  Γ Ψ Φ Δ₁ Ω₂ X Y A B
... | action₁ ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e₁) e₂
... | action₂ ctx ctx≡ f = f e₁ (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e₂)
-}
-}
admissibility-of-cut Γ Δ  Δ₁ Δ₂ _ _ p (impl-Lʳ Ω₁ {Ω₂} {A} {B} d) e = {!!}
{-
  subst-Sqnt-Γ obligation₂
  (impl-Lʳ (Δ₁ ++ Ω₁) d1
  (subst-Sqnt-Γ obligation₁
  (admissibility-of-cut _ _ Δ₁ _ _ _ p d2 e)))
  where
    -- I.H. d2 e
    -- e′ : Sqnt (Δ ++ (ctx ++ d ∷ ctx′) ++ Δ′) b
    -- e′ = admissibility-of-cut Δ p d2 e

    obligation₁ : Δ₁ ++ (Ω₁ ++ B ∷ Ω₂) ++ Δ₂ ≡ (Δ₁ ++ Ω₁) ++ B ∷ Ω₂ ++ Δ₂
    obligation₁ = xs++[xs++xs]++xs≡[xs++xs]++xs++xs Δ₁ Ω₁ (B ∷ Ω₂) Δ₂

    obligation₂ : (Δ₁ ++ Ω₁) ++ A ⊸ʳ B ∷ Ψ ++ Ω₂ ++ Δ₂ ≡ Δ₁ ++ (Ω₁ ++ A ⊸ʳ B ∷ Ψ ++ Ω₂) ++ Δ₂
    obligation₂ = [xs++xs]++xs++xs++xs≡xs++[xs++xs++xs]++xs Δ₁ Ω₁ (A ⊸ʳ B ∷ Ψ) Ω₂ Δ₂
-}
admissibility-of-cut Γ Δ Δ₁ Δ₂ a b refl d (impl-Rʳ {Γ = Γ2} {A = c} {B = b2}  e) =
  impl-Rʳ (subst-Sqnt-Γ obligation₂ e′)
  where
    obligation₁ : (Δ₁ ++ [ a ] ++ Δ₂) ++ [ c ] ≡ Δ₁ ++ [ a ] ++ Δ₂ ++ [ c ]
    obligation₁ = [xs++xs++xs]++xs≡xs++xs++xs++xs Δ₁ [ a ] Δ₂ [ c ]

    e′ : Sqnt (Δ₁ ++ Γ ++ Δ₂ ++ [ c ]) b2
    e′ = admissibility-of-cut _ _ Δ₁ _ _ _ obligation₁ d e

    obligation₂ : Δ₁ ++ Γ ++ Δ₂ ++ [ c ] ≡ (Δ₁ ++ Γ ++ Δ₂) ++ [ c ]
    obligation₂ = xs++xs++xs++xs≡[xs++xs++xs]++xs Δ₁ Γ Δ₂ [ c ]

{-
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@(impl-R _)    (impl-Lʳ {Ψ} Ω₁ {Ω₂} {A} {B} e₁ e₂)
  with admit-app-L Γ Ψ Δ₁ Δ₂ Ω₁ Ω₂ A B X Y eq (λ ())
... | action₁ ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e₁) e₂
... | action₂ ctx ctx≡ f = f e₁ (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e₂)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@(times-R _ _) (impl-Lʳ {Ψ} Ω₁ {Ω₂} {A} {B} e₁ e₂)
  with admit-app-L Γ Ψ Δ₁ Δ₂ Ω₁ Ω₂ A B X Y eq (λ ())
... | action₁ ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e₁) e₂
... | action₂ ctx ctx≡ f = f e₁ (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e₂)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@(plus-R₁ _)   (impl-Lʳ {Ψ} Ω₁ {Ω₂} {A} {B} e₁ e₂)
  with admit-app-L Γ Ψ Δ₁ Δ₂ Ω₁ Ω₂ A B X Y eq (λ ())
... | action₁ ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e₁) e₂
... | action₂ ctx ctx≡ f = f e₁ (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e₂)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@(plus-R₂ _)   (impl-Lʳ {Ψ} Ω₁ {Ω₂} {A} {B} e₁ e₂)
  with admit-app-L Γ Ψ Δ₁ Δ₂ Ω₁ Ω₂ A B X Y eq (λ ())
... | action₁ ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e₁) e₂
... | action₂ ctx ctx≡ f = f e₁ (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e₂)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@(with-R _ _)  (impl-Lʳ {Ψ} Ω₁ {Ω₂} {A} {B} e₁ e₂)
  with admit-app-L Γ Ψ Δ₁ Δ₂ Ω₁ Ω₂ A B X Y eq (λ ())
... | action₁ ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e₁) e₂
... | action₂ ctx ctx≡ f = f e₁ (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e₂)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@unit-R        (impl-Lʳ {Ψ} Ω₁ {Ω₂} {A} {B} e₁ e₂)
  with admit-app-L Γ Ψ Δ₁ Δ₂ Ω₁ Ω₂ A B X Y eq (λ ())
... | action₁ ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e₁) e₂
... | action₂ ctx ctx≡ f = f e₁ (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e₂)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@top-R         (impl-Lʳ {Ψ} Ω₁ {Ω₂} {A} {B} e₁ e₂)
  with admit-app-L Γ Ψ Δ₁ Δ₂ Ω₁ Ω₂ A B X Y eq (λ ())
... | action₁ ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e₁) e₂
... | action₂ ctx ctx≡ f = f e₁ (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e₂)
-}

-- TIMES
------------------------------------------------------------------------

{-
admissibility-of-cut _ _ Δ₁ _ _ _ eq (times-R _ _) (times-L Ω₁ _) with match-cons Ω₁ Δ₁ eq
admissibility-of-cut _ _ Δ₁ Δ₂ _ X eq (times-R {Γ₁} {Γ₂} {A} {B} d₁ d₂) (times-L Ω₁ e) | here refl refl refl =
  subst-Sqnt-Γ obligation₂ e₂
  where
    obligation₁ : Ω₁ ++ Γ₁ ++ B ∷ Δ₂ ≡ (Ω₁ ++ Γ₁) ++ B ∷ Δ₂
    obligation₁ = xs++xs++xs≡[xs++xs]++xs Ω₁ Γ₁ (B ∷ Δ₂)

    obligation₂ : (Ω₁ ++ Γ₁) ++ Γ₂ ++ Δ₂ ≡ Ω₁ ++ (Γ₁ ++ Γ₂) ++ Δ₂
    obligation₂ = [xs++xs]++xs++xs≡xs++[xs++xs]++xs Ω₁ Γ₁ Γ₂ Δ₂

    e₁ : Sqnt (Ω₁ ++ Γ₁ ++ B ∷ Δ₂) X
    e₁ = admissibility-of-cut _ _ Ω₁ _ _ _ refl d₁ e

    e₂ : Sqnt ((Ω₁ ++ Γ₁) ++ Γ₂ ++ Δ₂) X
    e₂ = admissibility-of-cut _ _ (Ω₁ ++ Γ₁) _ _ _ obligation₁ d₂ e₁

admissibility-of-cut _ _ Δ₁ _ _ X eq d@(times-R {Γ₁} {Γ₂} {C} {D} _ _) (times-L Ω₁ {Ω₂} {A} {B} e) | before Ψ refl refl
  with admit-times-L-before (Γ₁ ++ Γ₂) Ψ Δ₁ Ω₂ A B (C ⊗ D) X
... | action ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e)
admissibility-of-cut _ _ _ Δ₂ _ X eq d@(times-R {Γ₁} {Γ₂} {C} {D} _ _) (times-L Ω₁ {_} {A} {B} e) | after Ψ refl refl
  with admit-times-L-after (Γ₁ ++ Γ₂) Ψ Ω₁ Δ₂ A B (C ⊗ D) X
... | action ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e)

admissibility-of-cut _ _ Δ₁ Δ₂ C D eq (times-L Ω₁ {Ω₂} {A} {B} d) e =
  process admissibility-of-cut _ _ Δ₁ _ _ _ eq d e by
    Δ₁ ++ (Ω₁ ++ A ∷ B ∷ Ω₂) ++ Δ₂ ⊢ D ≡Γ⟨ obligation₁ ⟩
    (Δ₁ ++ Ω₁) ++ A ∷ B ∷ Ω₂ ++ Δ₂ ⊢ D $⟨ times-L (Δ₁ ++ Ω₁) ⟩
    (Δ₁ ++ Ω₁) ++ A ⊗ B ∷ Ω₂ ++ Δ₂ ⊢ D ≡Γ⟨ obligation₂ ⟩
    Δ₁ ++ (Ω₁ ++ A ⊗ B ∷ Ω₂) ++ Δ₂ ⊢ D ∎
  where
    obligation₁ : Δ₁ ++ (Ω₁ ++ A ∷ B ∷ Ω₂) ++ Δ₂ ≡ (Δ₁ ++ Ω₁) ++ A ∷ B ∷ Ω₂ ++ Δ₂
    obligation₁ = xs++[xs++xs]++xs≡[xs++xs]++xs++xs Δ₁ Ω₁ (A ∷ B ∷ Ω₂) Δ₂

    obligation₂ : (Δ₁ ++ Ω₁) ++ A ⊗ B ∷ Ω₂ ++ Δ₂ ≡ Δ₁ ++ (Ω₁ ++ A ⊗ B ∷ Ω₂) ++ Δ₂
    obligation₂ = [xs++xs]++xs++xs≡xs++[xs++xs]++xs Δ₁ Ω₁ (A ⊗ B ∷ Ω₂) Δ₂

admissibility-of-cut _ _ Δ₁ _ _ _ eq d (times-R {Ω₁} e₁ e₂) with find-cons Ω₁ Δ₁ eq
admissibility-of-cut Γ _ Δ₁ _ _ _ _ d (times-R {Ω₁} {Ω₂} {A} {B} e₁ e₂) | in-first Ψ refl refl =
  process admissibility-of-cut _ _ Δ₁ _ _ _ refl d e₁ by
    Δ₁ ++ Γ ++ Ψ        ⊢ A     $⟨ (λ x → times-R x e₂) ⟩
    (Δ₁ ++ Γ ++ Ψ) ++ Ω₂ ⊢ A ⊗ B ≡Γ⟨ obligation₁ ⟩
    Δ₁ ++ Γ ++ Ψ ++ Ω₂   ⊢ A ⊗ B ∎
  where
    obligation₁ : (Δ₁ ++ Γ ++ Ψ) ++ Ω₂ ≡ Δ₁ ++ Γ ++ Ψ ++ Ω₂
    obligation₁ = [xs++xs++xs]++xs≡xs++xs++xs++xs Δ₁ Γ Ψ Ω₂

admissibility-of-cut Γ _ _ Δ₂ _ _ eq d (times-R {Ω₁} {_} {A} {B} e₁ e₂) | in-second Ψ refl refl =
  process admissibility-of-cut _ _ Ψ _ _ _ refl d e₂ by
    Ψ ++ Γ ++ Δ₂ ⊢ B $⟨ times-R e₁ ⟩
    Ω₁ ++ Ψ ++ Γ ++ Δ₂ ⊢ A ⊗ B ≡Γ⟨ obligation₁ ⟩
    (Ω₁ ++ Ψ) ++ Γ ++ Δ₂ ⊢ A ⊗ B ∎
  where
    obligation₁ : Ω₁ ++ Ψ ++ Γ ++ Δ₂ ≡ (Ω₁ ++ Ψ) ++ Γ ++ Δ₂
    obligation₁ = xs++xs++xs++xs≡[xs++xs]++xs++xs Ω₁ Ψ Γ Δ₂

admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@(impl-R _)    (times-L Ω₁ {Ω₂} {A} {B} e)
  with admit-times-L Γ Δ₁ Δ₂ Ω₁ Ω₂ A B Y X eq (λ ())
... | action ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@(impl-Rʳ _)   (times-L Ω₁ {Ω₂} {A} {B} e)
  with admit-times-L Γ Δ₁ Δ₂ Ω₁ Ω₂ A B Y X eq (λ ())
... | action ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@(plus-R₁ _)  (times-L Ω₁ {Ω₂} {A} {B} e)
  with admit-times-L Γ Δ₁ Δ₂ Ω₁ Ω₂ A B Y X eq (λ ())
... | action ctx ctx≡ f =  f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@(plus-R₂ _)  (times-L Ω₁ {Ω₂} {A} {B} e)
  with admit-times-L Γ Δ₁ Δ₂ Ω₁ Ω₂ A B Y X eq (λ ())
... | action ctx ctx≡ f =  f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@(with-R _ _) (times-L Ω₁ {Ω₂} {A} {B} e)
  with admit-times-L Γ Δ₁ Δ₂ Ω₁ Ω₂ A B Y X eq (λ ())
... | action ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@unit-R       (times-L Ω₁ {Ω₂} {A} {B} e)
  with admit-times-L Γ Δ₁ Δ₂ Ω₁ Ω₂ A B Y X eq (λ ())
... | action ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@top-R        (times-L Ω₁ {Ω₂} {A} {B} e)
  with admit-times-L Γ Δ₁ Δ₂ Ω₁ Ω₂ A B Y X eq (λ ())
... | action ctx ctx≡ f =  f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e)

-- PLUS
------------------------------------------------------------------------

admissibility-of-cut _ _ Δ₁ _ _ _ eq (plus-R₁ _) (plus-L Ω₁ _ _) with match-cons Ω₁ Δ₁ eq
admissibility-of-cut _ _ _ _ _ _ _  (plus-R₁ d) (plus-L Ω₁ e₁ _) | here refl refl refl
  = admissibility-of-cut _ _ Ω₁ _ _ _ refl d e₁
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X _ d@(plus-R₁ _) (plus-L Ω₁ {Ω₂} {C} {D} e₁ e₂) | before Ψ refl refl
  with admit-plus-L-before Γ Ψ Δ₁ Ω₂ C D Y X
... | action-both ctx₁ ctx≡₁ ctx₂ ctx≡₂ f = f
  (admissibility-of-cut _ _ ctx₁ _ _ _ ctx≡₁ d e₁)
  (admissibility-of-cut _ _ ctx₂ _ _ _ ctx≡₂ d e₂)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X _ d@(plus-R₁ _) (plus-L Ω₁ {Ω₂} {C} {D} e₁ e₂) | after Ψ refl refl
  with admit-plus-L-after Γ Ψ Ω₁ Δ₂ C D Y X
... | action-both ctx₁ ctx≡₁ ctx₂ ctx≡₂ f = f
  (admissibility-of-cut _ _ ctx₁ _ _ _ ctx≡₁ d e₁)
  (admissibility-of-cut _ _ ctx₂ _ _ _ ctx≡₂ d e₂)

admissibility-of-cut _ _ Δ₁ _ _ _ eq (plus-R₂ _) (plus-L Ω₁ _ _) with match-cons Ω₁ Δ₁ eq
admissibility-of-cut _ _ _ _ _ _ eq (plus-R₂ d) (plus-L Ω₁ _ e₂) | here refl refl refl
  = admissibility-of-cut _ _ Ω₁ _ _ _ refl d e₂

admissibility-of-cut Γ _ Δ₁ Δ₂ Y X _ d@(plus-R₂ _) (plus-L Ω₁ {Ω₂} {C} {D} e₁ e₂) | before Ψ refl refl
  with admit-plus-L-before Γ Ψ Δ₁ Ω₂ C D Y X
... | action-both ctx₁ ctx≡₁ ctx₂ ctx≡₂ f = f
  (admissibility-of-cut _ _ ctx₁ _ _ _ ctx≡₁ d e₁)
  (admissibility-of-cut _ _ ctx₂ _ _ _ ctx≡₂ d e₂)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X _ d@(plus-R₂ _) (plus-L Ω₁ {Ω₂} {C} {D} e₁ e₂) | after Ψ refl refl
  with admit-plus-L-after Γ Ψ Ω₁ Δ₂ C D Y X
... | action-both ctx₁ ctx≡₁ ctx₂ ctx≡₂ f = f
  (admissibility-of-cut _ _ ctx₁ _ _ _ ctx≡₁ d e₁)
  (admissibility-of-cut _ _ ctx₂ _ _ _ ctx≡₂ d e₂)

admissibility-of-cut _ _ Δ₁ Δ₂ C D eq (plus-L Ω₁ {Ω₂} {A} {B} d₁ d₂) e =
  subst-Sqnt-Γ obligation₁
  (plus-L (Δ₁ ++ Ω₁)
    (subst-Sqnt-Γ (obligation₂ A) (admissibility-of-cut _ _ Δ₁ _ _ _ eq d₁ e))
    (subst-Sqnt-Γ (obligation₂ B) (admissibility-of-cut _ _ Δ₁ _ _ _ eq d₂ e)))
  where
    obligation₁ : (Δ₁ ++ Ω₁) ++ A ⊕ B ∷ Ω₂ ++ Δ₂ ≡ Δ₁ ++ (Ω₁ ++ A ⊕ B ∷ Ω₂) ++ Δ₂
    obligation₁ = [xs++xs]++xs++xs≡xs++[xs++xs]++xs Δ₁ Ω₁ (A ⊕ B ∷ Ω₂) Δ₂

    obligation₂ : ∀ X → Δ₁ ++ (Ω₁ ++ X ∷ Ω₂) ++ Δ₂ ≡ (Δ₁ ++ Ω₁) ++ X ∷ Ω₂ ++ Δ₂
    obligation₂ X = xs++[xs++xs]++xs≡[xs++xs]++xs++xs Δ₁ Ω₁ (X ∷ Ω₂) Δ₂

admissibility-of-cut _ _ Δ₁ _ _ _ eq d (plus-R₁ e) = plus-R₁ (admissibility-of-cut _ _ Δ₁ _ _ _ eq d e)
admissibility-of-cut _ _ Δ₁ _ _ _ eq d (plus-R₂ e) = plus-R₂ (admissibility-of-cut _ _ Δ₁ _ _ _ eq d e)

admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@(impl-R _)    (plus-L Ω₁ {Ω₂} e₁ e₂)
  with admit-plus-L Γ Δ₁ Δ₂ Ω₁ Ω₂ _ _ _ _ eq (λ ())
... | action-both ctx₁ ctx≡₁ ctx₂ ctx≡₂ f = f
  (admissibility-of-cut _ _ ctx₁ _ _ _ ctx≡₁ d e₁)
  (admissibility-of-cut _ _ ctx₂ _ _ _ ctx≡₂ d e₂)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@(impl-Rʳ _)   (plus-L Ω₁ {Ω₂} e₁ e₂)
  with admit-plus-L Γ Δ₁ Δ₂ Ω₁ Ω₂ _ _ _ _ eq (λ ())
... | action-both ctx₁ ctx≡₁ ctx₂ ctx≡₂ f = f
  (admissibility-of-cut _ _ ctx₁ _ _ _ ctx≡₁ d e₁)
  (admissibility-of-cut _ _ ctx₂ _ _ _ ctx≡₂ d e₂)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@(times-R _ _) (plus-L Ω₁ {Ω₂} e₁ e₂)
  with admit-plus-L Γ Δ₁ Δ₂ Ω₁ Ω₂ _ _ _ _ eq (λ ())
... | action-both ctx₁ ctx≡₁ ctx₂ ctx≡₂ f = f
  (admissibility-of-cut _ _ ctx₁ _ _ _ ctx≡₁ d e₁)
  (admissibility-of-cut _ _ ctx₂ _ _ _ ctx≡₂ d e₂)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@(with-R _ _)  (plus-L Ω₁ {Ω₂} e₁ e₂)
  with admit-plus-L Γ Δ₁ Δ₂ Ω₁ Ω₂ _ _ _ _ eq (λ ())
... | action-both ctx₁ ctx≡₁ ctx₂ ctx≡₂ f = f
  (admissibility-of-cut _ _ ctx₁ _ _ _ ctx≡₁ d e₁)
  (admissibility-of-cut _ _ ctx₂ _ _ _ ctx≡₂ d e₂)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@unit-R        (plus-L Ω₁ {Ω₂} e₁ e₂)
  with admit-plus-L Γ Δ₁ Δ₂ Ω₁ Ω₂ _ _ _ _ eq (λ ())
... | action-both ctx₁ ctx≡₁ ctx₂ ctx≡₂ f = f
  (admissibility-of-cut _ _ ctx₁ _ _ _ ctx≡₁ d e₁)
  (admissibility-of-cut _ _ ctx₂ _ _ _ ctx≡₂ d e₂)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@top-R         (plus-L Ω₁ {Ω₂} e₁ e₂)
  with admit-plus-L Γ Δ₁ Δ₂ Ω₁ Ω₂ _ _ _ _ eq (λ ())
... | action-both ctx₁ ctx≡₁ ctx₂ ctx≡₂ f = f
  (admissibility-of-cut _ _ ctx₁ _ _ _ ctx≡₁ d e₁)
  (admissibility-of-cut _ _ ctx₂ _ _ _ ctx≡₂ d e₂)

-- WITH
------------------------------------------------------------------------

admissibility-of-cut _ _ Δ₁ _ _ _ eq (with-R d₁ d₂) (with-L₁ Ω₁ e) with match-cons Ω₁ Δ₁ eq
admissibility-of-cut _ _ Δ₁ _ _ _ eq (with-R d₁ d₂) (with-L₁ Ω₁ e) | here refl refl refl =
  admissibility-of-cut _ _ Δ₁ _ _ _ refl d₁ e
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X _ d@(with-R _ _) (with-L₁ Ω₁ {Ω₂} e) | before Ψ refl refl
  with admit-with-L-before₁ Γ Ψ Δ₁ Ω₂ _ _ Y X
... | action ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X _ d@(with-R _ _) (with-L₁ Ω₁ e) | after Ψ refl refl
  with admit-with-L-after₁ Γ Ψ Ω₁ Δ₂ _ _ Y X
... | action ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e)

admissibility-of-cut _ _ Δ₁ _ _ _ eq (with-R d₁ d₂) (with-L₂ Ω₁ e) with match-cons Ω₁ Δ₁ eq
admissibility-of-cut _ _ Δ₁ _ _ _ eq (with-R d₁ d₂) (with-L₂ Ω₁ e) | here refl refl refl =
  admissibility-of-cut _ _ Δ₁ _ _ _ refl d₂ e
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X _ d@(with-R _ _) (with-L₂ Ω₁ {Ω₂} e) | before Ψ refl refl
  with admit-with-L-before₂ Γ Ψ Δ₁ Ω₂ _ _ Y X
... | action ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X _ d@(with-R _ _) (with-L₂ Ω₁ e) | after Ψ refl refl
  with admit-with-L-after₂ Γ Ψ Ω₁ Δ₂ _ _ Y X
... | action ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e)

admissibility-of-cut _ _ Δ₁ _ _ _ eq  d (with-R e₁ e₂) = with-R
  (admissibility-of-cut _ _ Δ₁ _ _ _ eq d e₁)
  (admissibility-of-cut _ _ Δ₁ _ _ _ eq d e₂)

admissibility-of-cut _ _ Δ₁ Δ₂ _ _ eq (with-L₁ Ω₁ {Ω₂} {A} {B} d) e =
  subst-Sqnt-Γ obligation₁
  (with-L₁ (Δ₁ ++ Ω₁)
  (subst-Sqnt-Γ obligation₂
  (admissibility-of-cut _ _ Δ₁ _ _ _ eq d e)))
  where
    obligation₁ : (Δ₁ ++ Ω₁) ++ A & B ∷ Ω₂ ++ Δ₂ ≡ Δ₁ ++ (Ω₁ ++ A & B ∷ Ω₂) ++ Δ₂
    obligation₁ = [xs++xs]++xs++xs≡xs++[xs++xs]++xs Δ₁ Ω₁ (A & B ∷ Ω₂) Δ₂

    obligation₂ : Δ₁ ++ (Ω₁ ++ A ∷ Ω₂) ++ Δ₂ ≡ (Δ₁ ++ Ω₁) ++ A ∷ Ω₂ ++ Δ₂
    obligation₂ = xs++[xs++xs]++xs≡[xs++xs]++xs++xs Δ₁ Ω₁ (A ∷ Ω₂) Δ₂

admissibility-of-cut _ _ Δ₁ Δ₂ _ _ eq (with-L₂ Ω₁ {Ω₂} {A} {B} d) e =
  subst-Sqnt-Γ obligation₁
  (with-L₂ (Δ₁ ++ Ω₁)
  (subst-Sqnt-Γ obligation₂
  (admissibility-of-cut _ _ Δ₁ _ _ _ eq d e)))
  where
    obligation₁ : (Δ₁ ++ Ω₁) ++ A & B ∷ Ω₂ ++ Δ₂ ≡ Δ₁ ++ (Ω₁ ++ A & B ∷ Ω₂) ++ Δ₂
    obligation₁ = [xs++xs]++xs++xs≡xs++[xs++xs]++xs Δ₁ Ω₁ (A & B ∷ Ω₂) Δ₂

    obligation₂ : Δ₁ ++ (Ω₁ ++ B ∷ Ω₂) ++ Δ₂ ≡ (Δ₁ ++ Ω₁) ++ B ∷ Ω₂ ++ Δ₂
    obligation₂ = xs++[xs++xs]++xs≡[xs++xs]++xs++xs Δ₁ Ω₁ (B ∷ Ω₂) Δ₂

admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@(impl-R _)    (with-L₁ Ω₁ {Ω₂} {A} {B} e)
  with admit-with-L₁ Γ Δ₁ Δ₂ Ω₁ Ω₂ A B Y X eq (λ ())
... | action ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@(impl-Rʳ _)   (with-L₁ Ω₁ {Ω₂} {A} {B} e)
  with admit-with-L₁ Γ Δ₁ Δ₂ Ω₁ Ω₂ A B Y X eq (λ ())
... | action ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@(times-R _ _) (with-L₁ Ω₁ {Ω₂} {A} {B} e)
  with admit-with-L₁ Γ Δ₁ Δ₂ Ω₁ Ω₂ A B Y X eq (λ ())
... | action ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@(plus-R₁ _)   (with-L₁ Ω₁ {Ω₂} {A} {B} e)
  with admit-with-L₁ Γ Δ₁ Δ₂ Ω₁ Ω₂ A B Y X eq (λ ())
... | action ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@(plus-R₂ _)   (with-L₁ Ω₁ {Ω₂} {A} {B} e)
  with admit-with-L₁ Γ Δ₁ Δ₂ Ω₁ Ω₂ A B Y X eq (λ ())
... | action ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@unit-R        (with-L₁ Ω₁ {Ω₂} {A} {B} e)
  with admit-with-L₁ Γ Δ₁ Δ₂ Ω₁ Ω₂ A B Y X eq (λ ())
... | action ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@top-R         (with-L₁ Ω₁ {Ω₂} {A} {B} e)
  with admit-with-L₁ Γ Δ₁ Δ₂ Ω₁ Ω₂ A B Y X eq (λ ())
... | action ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e)

admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@(impl-R _)    (with-L₂ Ω₁ {Ω₂} {A} {B} e)
  with admit-with-L₂ Γ Δ₁ Δ₂ Ω₁ Ω₂ A B Y X eq (λ ())
... | action ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@(impl-Rʳ _)   (with-L₂ Ω₁ {Ω₂} {A} {B} e)
  with admit-with-L₂ Γ Δ₁ Δ₂ Ω₁ Ω₂ A B Y X eq (λ ())
... | action ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@(times-R _ _) (with-L₂ Ω₁ {Ω₂} {A} {B} e)
  with admit-with-L₂ Γ Δ₁ Δ₂ Ω₁ Ω₂ A B Y X eq (λ ())
... | action ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@(plus-R₁ _)   (with-L₂ Ω₁ {Ω₂} {A} {B} e)
  with admit-with-L₂ Γ Δ₁ Δ₂ Ω₁ Ω₂ A B Y X eq (λ ())
... | action ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@(plus-R₂ _)   (with-L₂ Ω₁ {Ω₂} {A} {B} e)
  with admit-with-L₂ Γ Δ₁ Δ₂ Ω₁ Ω₂ A B Y X eq (λ ())
... | action ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@unit-R        (with-L₂ Ω₁ {Ω₂} {A} {B} e)
  with admit-with-L₂ Γ Δ₁ Δ₂ Ω₁ Ω₂ A B Y X eq (λ ())
... | action ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@top-R         (with-L₂ Ω₁ {Ω₂} {A} {B} e)
  with admit-with-L₂ Γ Δ₁ Δ₂ Ω₁ Ω₂ A B Y X eq (λ ())
... | action ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e)

-- UNIT
------------------------------------------------------------------------

admissibility-of-cut _ _ Δ₁ _ _ b eq unit-R (unit-L Ω₁ e) with match-cons Ω₁ Δ₁ eq
admissibility-of-cut _ _ _ _ _ _ _ unit-R (unit-L _ e) | here refl refl refl = e
admissibility-of-cut _ _ Δ₁ _ _ B _ d@unit-R (unit-L _ {Ω₂} e) | before Ψ refl refl
  with admit-unit-L-before [] Ψ Δ₁ Ω₂ ♯1 B
... | action ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e)
admissibility-of-cut _ _ _ Δ₂ _ B _ d@unit-R (unit-L Ω₁ e) | after Ψ refl refl
  with admit-unit-L-after [] Ψ Ω₁ Δ₂ ♯1 B
... | action ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e)

admissibility-of-cut Γ Δ Δ₁ Δ₂ a b eq d unit-R = nil-cons-absurd Δ₁ eq
admissibility-of-cut Γ Δ Δ₁ Δ₂ A B eq (unit-L Ω₁ {Ω₂} d) e =
  subst-Sqnt-Γ obligation₁
  (unit-L (Δ₁ ++ Ω₁)
  (subst-Sqnt-Γ obligation₂
  (admissibility-of-cut (Ω₁ ++ Ω₂) _ Δ₁ Δ₂ _ _ eq d e)))
  where
    obligation₁ : (Δ₁ ++ Ω₁) ++ ♯1 ∷ Ω₂ ++ Δ₂ ≡ Δ₁ ++ (Ω₁ ++ ♯1 ∷ Ω₂) ++ Δ₂
    obligation₁ = [xs++xs]++xs++xs≡xs++[xs++xs]++xs Δ₁ Ω₁ (♯1 ∷ Ω₂) Δ₂

    obligation₂ : Δ₁ ++ (Ω₁ ++ Ω₂) ++ Δ₂ ≡ (Δ₁ ++ Ω₁) ++ Ω₂ ++ Δ₂
    obligation₂ = xs++[xs++xs]++xs≡[xs++xs]++xs++xs Δ₁ Ω₁ Ω₂ Δ₂

admissibility-of-cut Γ _ Δ₁ Δ₂ Y B eq d@(impl-R _)    (unit-L Ω₁ {Ω₂} e)
  with admit-unit-L Γ Δ₁ Δ₂ Ω₁ Ω₂ Y B eq (λ ())
... | action ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y B eq d@(impl-Rʳ _)   (unit-L Ω₁ {Ω₂} e)
  with admit-unit-L Γ Δ₁ Δ₂ Ω₁ Ω₂ Y B eq (λ ())
... | action ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@(times-R _ _) (unit-L Ω₁ {Ω₂} e)
  with admit-unit-L Γ Δ₁ Δ₂ Ω₁ Ω₂ Y X eq (λ ())
... | action ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@(plus-R₁ _)   (unit-L Ω₁ {Ω₂} e)
  with admit-unit-L Γ Δ₁ Δ₂ Ω₁ Ω₂ Y X eq (λ ())
... | action ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@(plus-R₂ _)   (unit-L Ω₁ {Ω₂} e)
  with admit-unit-L Γ Δ₁ Δ₂ Ω₁ Ω₂ Y X eq (λ ())
... | action ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@(with-R _ _)  (unit-L Ω₁ {Ω₂} e)
  with admit-unit-L Γ Δ₁ Δ₂ Ω₁ Ω₂ Y X eq (λ ())
... | action ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e)
admissibility-of-cut Γ _ Δ₁ Δ₂ Y X eq d@top-R         (unit-L Ω₁ {Ω₂} e)
  with admit-unit-L Γ Δ₁ Δ₂ Ω₁ Ω₂ Y X eq (λ ())
... | action ctx ctx≡ f = f (admissibility-of-cut _ _ ctx _ _ _ ctx≡ d e)

-- ZERO
------------------------------------------------------------------------

admissibility-of-cut Γ Δ Δ₁ Δ₂ a b eq (zero-L Ω₁ {Ω₂}) e =
  subst-Sqnt-Γ obligation₁ (zero-L (Δ₁ ++ Ω₁))
  where
    obligation₁ : (Δ₁ ++ Ω₁) ++ ♯0 ∷ Ω₂ ++ Δ₂ ≡ Δ₁ ++ (Ω₁ ++ ♯0 ∷ Ω₂) ++ Δ₂
    obligation₁ = [xs++xs]++xs++xs≡xs++[xs++xs]++xs Δ₁ Ω₁ (♯0 ∷ Ω₂) Δ₂

admissibility-of-cut Γ Δ Δ₁ Δ₂ a b eq d (zero-L Ω₁ {Ω₂} ) with match-cons Ω₁ Δ₁ eq
admissibility-of-cut Γ _ Δ₁ Δ₂ _ B eq d (zero-L Ω₁ {Ω₂}) | here refl refl refl =
  absurd-T0 Γ Ω₁ Δ₂ B d

admissibility-of-cut Γ _ Δ₁ Δ₂ _ _ _ d (zero-L Ω₁ {Ω₂}) | before Ψ refl refl =
  subst-Sqnt-Γ obligation₁ (zero-L (Δ₁ ++ Γ ++ Ψ))
  where
    obligation₁ : (Δ₁ ++ Γ ++ Ψ) ++ ♯0 ∷ Ω₂ ≡ Δ₁ ++ Γ ++ Ψ ++ ♯0 ∷ Ω₂
    obligation₁ = [xs++xs++xs]++xs≡xs++xs++xs++xs Δ₁ Γ Ψ (♯0 ∷ Ω₂)

admissibility-of-cut Γ _ Δ₁ Δ₂ _ _ _ d (zero-L Ω₁ {Ω₂}) | after Ψ refl refl =
  subst-Sqnt-Γ obligation₁ (zero-L Ω₁)
  where
    obligation₁ : Ω₁ ++ ♯0 ∷ Ψ ++ Γ ++ Δ₂ ≡ (Ω₁ ++ ♯0 ∷ Ψ) ++ Γ ++ Δ₂
    obligation₁ = xs++xs++xs≡[xs++xs]++xs Ω₁ (♯0 ∷ Ψ) (Γ ++ Δ₂)

-- TOP
------------------------------------------------------------------------

admissibility-of-cut _ _ _ _ _ _ _ _ top-R = top-R
-}
