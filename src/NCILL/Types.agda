module NCILL.Types where

open import Data.Nat

-- TYPES
------------------------------------------------------------------------

data Ty : Set where
  κ    : ℕ → Ty
  _⊸_  : Ty → Ty → Ty
  _⊸ʳ_ : Ty → Ty → Ty -- either reversed, or argument on the right.
  _⊗_  : Ty → Ty → Ty
  _⊕_  : Ty → Ty → Ty
  _&_  : Ty → Ty → Ty
  ♯1   : Ty
  ♯0   : Ty
  ♯⊤   : Ty

infixr 8  _⊸_
infixr 8  _⊸ʳ_
infixr 9  _⊕_
infixr 10 _&_
infixr 11 _⊗_
