module NCILL.Examples.EtaBeta where

open import NCILL

open import Data.Empty
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Cut is admissible, but proof objects can still have roundabouts:
-- there might be possible η-reductions to be made.
------------------------------------------------------------------------

times-η : ∀ A B → [ A ⊗ B ] ⊢ A ⊗ B
times-η  _ _ = times-L [] (times-R var var) 

times-η′ : ∀ A B → [ A ⊗ B ] ⊢ A ⊗ B
times-η′ _ _ = var

times-η≢η′ : (∀ A B → times-η A B ≡ times-η′ A B) → ⊥
times-η≢η′ f with f ♯1 ♯1
times-η≢η′ f | ()

-- Compare that to β-reduction, CUT /is/ admissible.

times-β : ∀ A B C → A ∷ B ∷ [] ⊢ C → A ∷ B ∷ [] ⊢ C
times-β _ _ _ s = cut [] (times-R var var) (times-L [] s)

times-β′ : ∀ A B C → A ∷ B ∷ [] ⊢ C → A ∷ B ∷ [] ⊢ C
times-β′ _ _ _ s = s

times-β≡β′ : ∀ A B C → times-β A B C ≡ times-β′ A B C
times-β≡β′ _ _ _ = refl

-- Yet Agda is smarter, for record (with product as special example)

agda-pair-η : ∀ {a} → (A B : Set a) → (p :  A × B) → (proj₁ p ,  proj₂ p) ≡ p
agda-pair-η _ _ _ = refl

agda-pair-β :  ∀ {a} → (A B C : Set a)
  → (f : A → B → C)
  → f ≡ (λ x y → let p = x , y in f (proj₁ p) (proj₂ p)) 
agda-pair-β _ _ _ _f = refl

-- Importantly (Eta) extensionality doesn't apply to functions in Agda! See:

open import Relation.Binary.PropositionalEquality using (Extensionality)
