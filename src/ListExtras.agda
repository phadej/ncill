module ListExtras where

open import Data.List
open import Data.Nat
open import Data.Fin using (Fin; zero; suc)
open import Data.Product

open import Data.List.Properties using (++-assoc) renaming (++-identityʳ to ++-id-right; ∷-injectiveˡ to ∷-inj₁; ∷-injectiveʳ to ∷-inj₂) public

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans; subst) public

open import Simple-list-solver using (list-solve; bla) renaming (id to :[]; _⊕_ to _:++_; _⊜_ to _:≡_) public

nil-cons-absurd : ∀ {a b} {A : Set a} {B : Set b} (xs : List A) {y zs}
  → [] ≡ xs ++ y ∷ zs
  → B
nil-cons-absurd [] ()
nil-cons-absurd (x ∷ Γ) ()

singleton-lemma : ∀ {a} {A : Set a} (ys : List A) {x₁ x₂ zs}
  → [ x₁ ] ≡ ys ++ x₂ ∷ zs
  → ys ≡ [] × x₁ ≡ x₂ × zs ≡ []
singleton-lemma [] refl   = refl , refl , refl
singleton-lemma (_ ∷ Γ) p = nil-cons-absurd Γ (∷-inj₂ p)

data MatchCons {a} {A : Set a}
  (xs : List A) (y : A) (zs : List A)
  (us : List A) (v : A) (ws : List A) : Set a where
  here
    : xs ≡ us
    → y  ≡ v
    → zs ≡ ws
    → MatchCons xs y zs us v ws
  before : (ms : List A)
    → xs ≡ us ++ v ∷ ms
    → ms ++ y ∷ zs ≡ ws
    → MatchCons xs y zs us v ws
  after : (ms : List A)
    → zs ≡ ms ++ v ∷ ws
    → us ≡ xs ++ y ∷ ms
    → MatchCons xs y zs us v ws

match-cons : ∀ {a} {A : Set a}
  → (xs us : List A)
  → {zs ws : List A}
  → {y v : A}
  → xs ++ y ∷ zs ≡ us ++ v ∷ ws
  → MatchCons xs y zs us v ws
match-cons []       []       refl = here refl refl refl
match-cons []       (u ∷ us) p    = after us (∷-inj₂ p) (cong (λ i → i ∷ us) (sym (∷-inj₁ p)))
match-cons (x ∷ xs) []       p    = before xs (cong (λ i → i ∷ xs) (∷-inj₁ p)) (∷-inj₂ p)
match-cons (x ∷ xs) (u ∷ us) p with ∷-inj₁ p | match-cons xs us (∷-inj₂ p)
... | refl | here refl refl refl = here refl refl refl
... | refl | before ms refl refl = before ms refl refl
... | refl | after  ms refl refl = after  ms refl refl

match-cons-2 : ∀ {a} {A : Set a}
  → (xs xs′ us : List A)
  → {zs ws : List A}
  → {y v : A}
  → xs ++ xs′ ++ y ∷ zs ≡ us ++ v ∷ ws
  → MatchCons (xs ++ xs′) y zs us v ws
match-cons-2 [] [] [] refl = here refl refl refl
match-cons-2 [] (x ∷ xs′) [] p = before xs′ (cong (λ i → i ∷ xs′) (∷-inj₁ p)) (∷-inj₂ p)
match-cons-2 (x ∷ xs) xs′ [] p = before
  (xs ++ xs′)
  (cong (λ i → i ∷ xs ++ xs′) (∷-inj₁ p))
  (trans (++-assoc xs xs′ _) (∷-inj₂ p))
match-cons-2 [] [] (u ∷ us) p = after
  us
  (∷-inj₂ p)
  (sym (cong (λ i → i ∷ us) (∷-inj₁ p)))
match-cons-2 [] (x ∷ xs′) (u ∷ us) p with ∷-inj₁ p | match-cons xs′ us (∷-inj₂ p)
... | refl | here refl refl refl = here refl refl refl
... | refl | before ms refl refl = before ms refl refl
... | refl | after  ms refl refl = after ms refl refl
match-cons-2 (x ∷ xs) xs′ (u ∷ us) p with ∷-inj₁ p | match-cons-2 xs xs′ us (∷-inj₂ p)
... | refl | here refl refl refl = here refl refl refl
... | refl | before ms pf   refl = before ms (cong (λ is → x ∷ is) pf) refl
... | refl | after  ms refl refl = after ms refl refl

data FindCons {a} {A : Set a}
  (xs : List A) (ys : List A)
  (us : List A) (v : A) (ws : List A) : Set a where
  in-first : (ms : List A)
    → xs ≡ us ++ v ∷ ms
    → ms ++ ys ≡ ws
    → FindCons xs ys us v ws
  in-second : (ms : List A)
    → ys ≡ ms ++ v ∷ ws
    → xs ++ ms ≡ us
    → FindCons xs ys us v ws

find-cons : ∀ {a} {A : Set a}
  → (xs : List A) {ys : List A}
  → (us : List A) {v : A} {ws : List A}
  → xs ++ ys ≡ us ++ v ∷ ws
  → FindCons xs ys us v ws
find-cons []       []       refl = in-second [] refl refl
find-cons []       (u ∷ us) refl = in-second (u ∷ us) refl refl
find-cons (x ∷ xs) []       refl = in-first xs refl refl
find-cons (x ∷ xs) (x₁ ∷ us) p with ∷-inj₁ p | find-cons xs us (∷-inj₂ p)
... | refl | in-first  ms refl refl = in-first ms refl refl
... | refl | in-second ms refl refl = in-second ms refl refl
