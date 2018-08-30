module NCILL.Examples.Equivalences where

open import NCILL

-- All equivalences in Girard's paper (applicable to ILL)
-- are possible in NCILL, except commutativity of ⊗

-- Linear equivalence
------------------------------------------------------------------------

-- | Linear equivalence: A ⊢ B and B ⊢ A are provable
record _o-o_ (A B : Ty) : Set where
  field
    lfwd : [ A ] ⊢ B
    lbwd : [ B ] ⊢ A

infix 6 _o-o_

o-o-refl : ∀ A → A o-o A
o-o-refl _ = record { lfwd = var ; lbwd = var }

o-o-trans : ∀ A B C → A o-o B → B o-o C → A o-o C
o-o-trans _ _ _ record { lfwd = ab ; lbwd = ba } record { lfwd = bc ; lbwd = cb } = record
  { lfwd = cut [] ab bc
  ; lbwd = cut [] cb ba
  }

-- ♯1 and ⊗
------------------------------------------------------------------------

⊗-left-identity : ∀ A → ♯1 ⊗ A o-o A
⊗-left-identity _ = record
  { lfwd = times-L [] (unit-L [] var)
  ; lbwd = times-R unit-R var
  }

⊗-right-identity : ∀ A → A ⊗ ♯1 o-o A
⊗-right-identity _ = record
  { lfwd = times-L [] (unit-L [ _ ] var)
  ; lbwd = times-R var unit-R
  }

⊗-assoc : ∀ A B C → (A ⊗ B) ⊗ C o-o A ⊗ B ⊗ C
⊗-assoc _ _ _ = record
  { lfwd = times-L [] (times-L [] (times-R var (times-R var var)))
  ; lbwd = times-L [] (times-L [ _ ] (times-R (times-R var var) var))
  }

-- Note: ⊗ is not commutative!

-- ♯0 and ⊕
------------------------------------------------------------------------

⊕-left-identity : ∀ A → ♯0 ⊕ A o-o A
⊕-left-identity _ = record
  { lfwd = plus-L [] (zero-L []) var
  ; lbwd = plus-R₂ var
  }

⊕-right-identity : ∀ A → A ⊕ ♯0 o-o A
⊕-right-identity _ = record
  { lfwd = plus-L [] var (zero-L [])
  ; lbwd = plus-R₁ var
  }

⊕-assoc : ∀ A B C → (A ⊕ B) ⊕ C o-o A ⊕ B ⊕ C
⊕-assoc _ _ _ = record
  { lfwd = plus-L [] (plus-L [] (plus-R₁ var) (plus-R₂ (plus-R₁ var))) (plus-R₂ (plus-R₂ var))
  ; lbwd = plus-L [] (plus-R₁ (plus-R₁ var)) (plus-L [] (plus-R₁ (plus-R₂ var)) (plus-R₂ var))
  }

⊕-comm : ∀ A B → A ⊕ B o-o B ⊕ A
⊕-comm _ _ = record
  { lfwd = plus-L [] (plus-R₂ var) (plus-R₁ var)
  ; lbwd = plus-L [] (plus-R₂ var) (plus-R₁ var)
  }

-- not an isomorphism!
⊕-idemp : ∀ A → A ⊕ A o-o A
⊕-idemp _ = record
  { lfwd = plus-L [] var var
  ; lbwd = plus-R₁ var -- could be plus-R₂ too
  }

-- ♯⊤ and &
------------------------------------------------------------------------

&-left-identity : ∀ A → ♯⊤ & A o-o A
&-left-identity _ = record
  { lfwd = with-L₂ [] var
  ; lbwd = with-R top-R var
  }

&-right-identity : ∀ A → A & ♯⊤ o-o A
&-right-identity _ = record
  { lfwd = with-L₁ [] var
  ; lbwd = with-R var top-R
  }

&-assoc : ∀ A B C → (A & B) & C o-o A & B & C
&-assoc _ _ _ = record
  { lfwd = with-R
    (with-L₁ [] (with-L₁ [] var))
    (with-R
      (with-L₁ [] (with-L₂ [] var))
      (with-L₂ [] var))
  ; lbwd = with-R
    (with-R
      (with-L₁ [] var)
      (with-L₂ [] (with-L₁ [] var)))
    (with-L₂ [] (with-L₂ [] var))
  }

&-comm : ∀ A B → A & B o-o B & A
&-comm _ _ = record
  { lfwd = with-R (with-L₂ [] var) (with-L₁ [] var)
  ; lbwd = with-R (with-L₂ [] var) (with-L₁ [] var)
  }

-- not an isomorphism!
&-idemp : ∀ A → A & A o-o A
&-idemp _ = record
  { lfwd = with-L₁ [] var
  ; lbwd = with-R var var
  }

-- Distributivity
------------------------------------------------------------------------

⊗-⊕-left-distr : ∀ A B C → A ⊗ (B ⊕ C) o-o (A ⊗ B) ⊕ (A ⊗ C)
⊗-⊕-left-distr _ _ _ = record
  { lfwd = times-L [] (plus-L [ _ ]
    (plus-R₁ (times-R var var))
    (plus-R₂ (times-R var var)))
  ; lbwd = plus-L []
    (times-L [] (times-R var (plus-R₁ var)))
    (times-L [] (times-R var (plus-R₂ var)))
  }
  
⊗-⊕-right-distr : ∀ A B C → (A ⊕ B) ⊗ C o-o (A ⊗ C) ⊕ (B ⊗ C)
⊗-⊕-right-distr _ _ _ = record
  { lfwd = times-L [] (plus-L []
    (plus-R₁ (times-R var var))
    (plus-R₂ (times-R var var)))
  ; lbwd = plus-L []
    (times-L [] (times-R (plus-R₁ var) var))
    (times-L [] (times-R (plus-R₂ var) var))
  }

left-zero : ∀ A → ♯0 ⊗ A o-o ♯0
left-zero _ = record
  { lfwd = times-L [] (zero-L [])
  ; lbwd = zero-L []
  }

right-zero : ∀ A → A ⊗ ♯0 o-o ♯0
right-zero _ = record
  { lfwd = times-L [] (zero-L [ _ ])
  ; lbwd = zero-L []
  }

absurd : ∀ A → ♯0 ⊸ʳ A o-o ♯⊤
absurd _ = record
  { lfwd = top-R
  ; lbwd = lam (zero-L (♯⊤ ∷ []))
  }

boring : ∀ A → A ⊸ʳ ♯⊤ o-o ♯⊤
boring _ = record
  { lfwd = top-R
  ; lbwd = lam top-R
  }

distr-1 : ∀ A B C → A ⊕ B ⊸ʳ C o-o (A ⊸ʳ C) & (B ⊸ʳ C)
distr-1 _ _ _ = record
  { lfwd = with-R
    (lam (app [] (plus-R₁ var) var))
    (lam (app [] (plus-R₂ var) var))
  ; lbwd = lam (plus-L [ _ ]
    (with-L₁ [] (app [] var var))
    (with-L₂ [] (app [] var var)))
  }

distr-2 : ∀ A B C → A ⊸ʳ B & C o-o (A ⊸ʳ B) & (A ⊸ʳ C)
distr-2 _ _ _ = record
  { lfwd = with-R
    (lam (app [] var (with-L₁ [] var)))
    (lam (app [] var (with-L₂ [] var)))
  ; lbwd = lam (with-R
    (with-L₁ [] (app [] var var))
    (with-L₂ [] (app [] var var)))
  }

-- Half-distributivity
------------------------------------------------------------------------

-- This is interesting, why it works only in one direction!
half-distr-1 : ∀ A B C → [ A ⊗ (B & C) ] ⊢ (A ⊗ B) & (A ⊗ C)
half-distr-1 _ _ _ = with-R
  (times-L [] (times-R var (with-L₁ [] var)))
  (times-L [] (times-R var (with-L₂ [] var)))

-- half-distr-1-rev : ∀ A B C → Sqnt [ (A ⊗ B) & (A ⊗ C) ] (A ⊗ (B & C)) 
-- half-distr-1-rev _ _ _ = ?

half-distr-2 : ∀ A B C → [ (A ⊸ʳ C) ⊕ (B ⊸ʳ C) ] ⊢ A & B ⊸ʳ C
half-distr-2 _ _ _ = lam (plus-L []
  (app [] (with-L₁ [] var) var)
  (app [] (with-L₂ [] var) var))

half-distr-3 : ∀ A B C → [ (A ⊸ʳ B) ⊕ (A ⊸ʳ C) ] ⊢ A ⊸ʳ B ⊕ C
half-distr-3 _ _ _ = lam (plus-L []
  (app [] var (plus-R₁ var))
  (app [] var (plus-R₂ var)) )

-- ⊗ and ⊸ are adjoint
------------------------------------------------------------------------

-- We need CUT in the forward direction
-- Also see how ⊸ "swaps" ⊗ halfs.
--
-- /This/ makes me think that I (and my references) have ⊸ and ⊸ʳ in the wrong way
--
curry : ∀ A B C → B ⊗ A ⊸ C o-o A ⊸ B ⊸ C
curry _ _ _ = record
  { lfwd = impl-R (impl-R (cut [] (times-R var var) (impl-L [] var var)))
  ; lbwd = impl-R (times-L [] (impl-L [ _ ] var (impl-L [] var var)))
  }

curryʳ : ∀ A B C → A ⊗ B ⊸ʳ C o-o A ⊸ʳ B ⊸ʳ C
curryʳ _ _ _ = record
  { lfwd = impl-Rʳ (impl-Rʳ (cut [ _ ] (times-R var var) (impl-Lʳ [] var var)))
  ; lbwd = impl-Rʳ (times-L [ _ ] (impl-Lʳ [] var (impl-Lʳ [] var var)))
  }

-- Implication equivalence
------------------------------------------------------------------------

-- Note: this equivalence is weaker than o-o !

lin-equiv₁ : ∀ A B → [] ⊢ A ⊸ B → [] ⊢ A ⊸ʳ B
lin-equiv₁ _ _ f = impl-Rʳ (cut [ _ ] f (impl-L [] var var))

lin-equiv₂ : ∀ A B → [] ⊢ A ⊸ʳ B → [] ⊢ A ⊸ B
lin-equiv₂ _ _ f = impl-R (cut [] f (impl-Lʳ [] var var))
