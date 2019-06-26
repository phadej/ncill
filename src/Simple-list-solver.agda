module Simple-list-solver where

open import Data.Nat
open import Data.Fin using (Fin; zero; suc; inject+)
open import Data.List
open import Data.List.Properties
open import Data.Product
open import Data.Vec using(Vec; []; _∷_; lookup)

open import Data.Nat.Properties
import Data.Vec.Properties as V

open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; cong₂; subst)
open Relation.Binary.PropositionalEquality.≡-Reasoning

data AutoExpr : ℕ → Set where
  bla : AutoExpr 1
  id  : AutoExpr 0
  _⊕_ : ∀ {n m} → AutoExpr n → AutoExpr m → AutoExpr (n + m)

infixr 5 _⊕_
infixr 4 _⊜_

_⊜_ : ∀ {n} → AutoExpr n → AutoExpr n → AutoExpr n × AutoExpr n
e₁ ⊜ e₂ = e₁ , e₂

⟦_⟧_ : ∀ {n a} {A : Set a} → (e : AutoExpr n) → Vec (List A) n → List A
⟦ bla    ⟧ (x ∷ []) = x
⟦ id     ⟧ []       = []
⟦ _⊕_ {n} e₁ e₂ ⟧ ρ with Data.Vec.splitAt n ρ
⟦ e₁ ⊕ e₂ ⟧ ρ | ρ₁ , ρ₂ , _ = ⟦ e₁ ⟧ ρ₁ ++ ⟦ e₂ ⟧ ρ₂

infixl 9 ⟦_⟧_

-- -- "Normalise"
normalize : ∀ {n a} {A : Set a} → Vec (List A) n → List A
normalize []      = []
normalize (x ∷ v) = x ++ normalize v

normalize-++ : ∀ {n m a} {A : Set a}
  → (xs : Vec (List A) n)
  → (ys : Vec (List A) m)
  → (zs : Vec (List A) (n + m))
  → xs Data.Vec.++ ys ≡ zs
  → normalize xs ++ normalize ys ≡ normalize zs
normalize-++ []       ys zs       eq = cong normalize eq
normalize-++ (x ∷ xs) ys (z ∷ zs) eq = begin
  (x ++ normalize xs) ++ normalize ys ≡⟨ ++-assoc x (normalize xs) (normalize ys) ⟩
  x ++ normalize xs ++ normalize ys   ≡⟨ cong₂ _++_ (V.∷-injectiveˡ eq) (normalize-++ xs ys zs (V.∷-injectiveʳ eq)) ⟩
  z ++ normalize zs                 ∎

lemma : ∀ {n a} {A : Set a}
   → (e : AutoExpr n)
   → (ρ : Vec (List A) n)
   → ⟦ e ⟧ ρ ≡ normalize ρ
lemma bla (x ∷ []) = sym (++-identityʳ x)
lemma id []  = refl
lemma (_⊕_ {n} e₁ e₂) ρ with Data.Vec.splitAt n ρ
... | ρ₁ , ρ₂ , ρ-assoc with lemma e₁ ρ₁ | lemma e₂ ρ₂
... | eq₁ | eq₂ = begin
  ⟦ e₁ ⟧ ρ₁   ++ ⟦ e₂ ⟧ ρ₂     ≡⟨ cong₂ _++_ eq₁ eq₂ ⟩
  normalize ρ₁ ++ normalize ρ₂   ≡⟨ normalize-++ ρ₁ ρ₂ ρ (sym ρ-assoc) ⟩
  normalize ρ                 ∎

theorem : ∀ {a n} {A : Set a}
  → (e₁ : AutoExpr n)
  → (e₂ : AutoExpr n)
  → (ρ : Vec (List A) n)
  → ⟦ e₁ ⟧ ρ ≡ ⟦ e₂ ⟧ ρ
theorem e₁ e₂ ρ with lemma e₁ ρ | lemma e₂ ρ
... | l | k  = trans l (sym k)

list-solve-type : ∀ {a} {A : Set a} (n : ℕ)
  → (Vec (List A) n → Set a)
  → Set a
list-solve-type         zero    f = f []
list-solve-type {A = A} (suc n) f =
  (xs : List A) → list-solve-type n (λ vs → f (xs ∷ vs))

list-solve-impl : ∀ {a} {A : Set a} (n : ℕ)
  → (f : Vec (List A) n → Set a)
  → (g : (ρ : Vec (List A) n) → f ρ)
  → list-solve-type {A = A} n (λ ρ → f ρ)
list-solve-impl zero    f g = g []
list-solve-impl(suc n) f g = λ xs → list-solve-impl n
  (λ vs → f (xs ∷ vs)) (λ vs → g (xs ∷ vs))

-- list-solve-type 3 = λ f → (xs₁ xs₂ xs₃: List A) → f (xs₁ ∷ xs₂ ∷ xs₃ ∷ [])
list-solve : ∀ {a n} {A : Set a}
  → (es : AutoExpr n × AutoExpr n)
  → list-solve-type {A = A} n (λ ρ → ⟦ proj₁ es ⟧ ρ ≡ ⟦ proj₂ es ⟧ ρ)
list-solve {n = n} (e₁ , e₂ ) = list-solve-impl n _ λ ρ → theorem e₁ e₂ ρ

-- DEMOS
--------------

private
  ++-assoc-again : ∀ {a} → {A : Set a}
    → (xs : List A)
    → (ys : List A)
    → (zs : List A)
    → xs ++ ys ++ zs ≡ (xs ++ ys) ++ zs
  ++-assoc-again = list-solve
    (bla ⊕ bla ⊕ bla ⊜ (bla ⊕ bla) ⊕ bla)

  crazier : ∀ {a} → {A : Set a}
    → (xs : List A)
    → (ys : List A)
    → (zs : List A)
    → (ws : List A)
    → xs ++ (ys ++ zs) ++ ws ≡ (xs ++ ys) ++ (zs ++ ws)
  crazier = list-solve
    (bla ⊕ (bla ⊕ bla) ⊕ bla ⊜ (bla ⊕ bla) ⊕ (bla ⊕ bla))
