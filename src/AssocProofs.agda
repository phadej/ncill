module AssocProofs where

open import Data.List
open import Data.Nat

open import ListExtras

-- ASSOCIATIVITY FOR FORMULAS OF SIZE 3
------------------------------------------------------------------------

[xs++xs]++xs≡xs++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs : List A)
  → (as ++ bs) ++ cs ≡ as ++ bs ++ cs
[xs++xs]++xs≡xs++xs++xs = list-solve
  ((bla :++ bla) :++ bla :≡ bla :++ bla :++ bla)

xs++xs++xs≡[xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs : List A)
  → as ++ bs ++ cs ≡ (as ++ bs) ++ cs
xs++xs++xs≡[xs++xs]++xs = list-solve
  (bla :++ bla :++ bla :≡ (bla :++ bla) :++ bla)

-- ASSOCIATIVITY FOR FORMULAS OF SIZE 4
------------------------------------------------------------------------

xs++[xs++xs]++xs≡xs++xs++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds : List A)
  → as ++ (bs ++ cs) ++ ds ≡ as ++ bs ++ cs ++ ds
xs++[xs++xs]++xs≡xs++xs++xs++xs = list-solve
  (bla :++ (bla :++ bla) :++ bla :≡ bla :++ bla :++ bla :++ bla)

[xs++xs]++xs++xs≡xs++xs++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds : List A)
  → (as ++ bs) ++ cs ++ ds ≡ as ++ bs ++ cs ++ ds
[xs++xs]++xs++xs≡xs++xs++xs++xs = list-solve
  ((bla :++ bla) :++ bla :++ bla :≡ bla :++ bla :++ bla :++ bla)

[xs++xs++xs]++xs≡xs++xs++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds : List A)
  → (as ++ bs ++ cs) ++ ds ≡ as ++ bs ++ cs ++ ds
[xs++xs++xs]++xs≡xs++xs++xs++xs = list-solve
  ((bla :++ bla :++ bla) :++ bla :≡ bla :++ bla :++ bla :++ bla)

[[xs++xs]++xs]++xs≡xs++xs++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds : List A)
  → ((as ++ bs) ++ cs) ++ ds ≡ as ++ bs ++ cs ++ ds
[[xs++xs]++xs]++xs≡xs++xs++xs++xs = list-solve
  (((bla :++ bla) :++ bla) :++ bla :≡ bla :++ bla :++ bla :++ bla)

xs++xs++xs++xs≡xs++[xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds : List A)
  → as ++ bs ++ cs ++ ds ≡ as ++ (bs ++ cs) ++ ds
xs++xs++xs++xs≡xs++[xs++xs]++xs = list-solve
  (bla :++ bla :++ bla :++ bla :≡ bla :++ (bla :++ bla) :++ bla)

[xs++xs]++xs++xs≡xs++[xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds : List A)
  → (as ++ bs) ++ cs ++ ds ≡ as ++ (bs ++ cs) ++ ds
[xs++xs]++xs++xs≡xs++[xs++xs]++xs = list-solve
  ((bla :++ bla) :++ bla :++ bla :≡ bla :++ (bla :++ bla) :++ bla)

[xs++xs++xs]++xs≡xs++[xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds : List A)
  → (as ++ bs ++ cs) ++ ds ≡ as ++ (bs ++ cs) ++ ds
[xs++xs++xs]++xs≡xs++[xs++xs]++xs = list-solve
  ((bla :++ bla :++ bla) :++ bla :≡ bla :++ (bla :++ bla) :++ bla)

[[xs++xs]++xs]++xs≡xs++[xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds : List A)
  → ((as ++ bs) ++ cs) ++ ds ≡ as ++ (bs ++ cs) ++ ds
[[xs++xs]++xs]++xs≡xs++[xs++xs]++xs = list-solve
  (((bla :++ bla) :++ bla) :++ bla :≡ bla :++ (bla :++ bla) :++ bla)

xs++xs++xs++xs≡[xs++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds : List A)
  → as ++ bs ++ cs ++ ds ≡ (as ++ bs) ++ cs ++ ds
xs++xs++xs++xs≡[xs++xs]++xs++xs = list-solve
  (bla :++ bla :++ bla :++ bla :≡ (bla :++ bla) :++ bla :++ bla)

xs++[xs++xs]++xs≡[xs++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds : List A)
  → as ++ (bs ++ cs) ++ ds ≡ (as ++ bs) ++ cs ++ ds
xs++[xs++xs]++xs≡[xs++xs]++xs++xs = list-solve
  (bla :++ (bla :++ bla) :++ bla :≡ (bla :++ bla) :++ bla :++ bla)

[xs++xs++xs]++xs≡[xs++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds : List A)
  → (as ++ bs ++ cs) ++ ds ≡ (as ++ bs) ++ cs ++ ds
[xs++xs++xs]++xs≡[xs++xs]++xs++xs = list-solve
  ((bla :++ bla :++ bla) :++ bla :≡ (bla :++ bla) :++ bla :++ bla)

[[xs++xs]++xs]++xs≡[xs++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds : List A)
  → ((as ++ bs) ++ cs) ++ ds ≡ (as ++ bs) ++ cs ++ ds
[[xs++xs]++xs]++xs≡[xs++xs]++xs++xs = list-solve
  (((bla :++ bla) :++ bla) :++ bla :≡ (bla :++ bla) :++ bla :++ bla)

xs++xs++xs++xs≡[xs++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds : List A)
  → as ++ bs ++ cs ++ ds ≡ (as ++ bs ++ cs) ++ ds
xs++xs++xs++xs≡[xs++xs++xs]++xs = list-solve
  (bla :++ bla :++ bla :++ bla :≡ (bla :++ bla :++ bla) :++ bla)

xs++[xs++xs]++xs≡[xs++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds : List A)
  → as ++ (bs ++ cs) ++ ds ≡ (as ++ bs ++ cs) ++ ds
xs++[xs++xs]++xs≡[xs++xs++xs]++xs = list-solve
  (bla :++ (bla :++ bla) :++ bla :≡ (bla :++ bla :++ bla) :++ bla)

[xs++xs]++xs++xs≡[xs++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds : List A)
  → (as ++ bs) ++ cs ++ ds ≡ (as ++ bs ++ cs) ++ ds
[xs++xs]++xs++xs≡[xs++xs++xs]++xs = list-solve
  ((bla :++ bla) :++ bla :++ bla :≡ (bla :++ bla :++ bla) :++ bla)

[[xs++xs]++xs]++xs≡[xs++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds : List A)
  → ((as ++ bs) ++ cs) ++ ds ≡ (as ++ bs ++ cs) ++ ds
[[xs++xs]++xs]++xs≡[xs++xs++xs]++xs = list-solve
  (((bla :++ bla) :++ bla) :++ bla :≡ (bla :++ bla :++ bla) :++ bla)

xs++xs++xs++xs≡[[xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds : List A)
  → as ++ bs ++ cs ++ ds ≡ ((as ++ bs) ++ cs) ++ ds
xs++xs++xs++xs≡[[xs++xs]++xs]++xs = list-solve
  (bla :++ bla :++ bla :++ bla :≡ ((bla :++ bla) :++ bla) :++ bla)

xs++[xs++xs]++xs≡[[xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds : List A)
  → as ++ (bs ++ cs) ++ ds ≡ ((as ++ bs) ++ cs) ++ ds
xs++[xs++xs]++xs≡[[xs++xs]++xs]++xs = list-solve
  (bla :++ (bla :++ bla) :++ bla :≡ ((bla :++ bla) :++ bla) :++ bla)

[xs++xs]++xs++xs≡[[xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds : List A)
  → (as ++ bs) ++ cs ++ ds ≡ ((as ++ bs) ++ cs) ++ ds
[xs++xs]++xs++xs≡[[xs++xs]++xs]++xs = list-solve
  ((bla :++ bla) :++ bla :++ bla :≡ ((bla :++ bla) :++ bla) :++ bla)

[xs++xs++xs]++xs≡[[xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds : List A)
  → (as ++ bs ++ cs) ++ ds ≡ ((as ++ bs) ++ cs) ++ ds
[xs++xs++xs]++xs≡[[xs++xs]++xs]++xs = list-solve
  ((bla :++ bla :++ bla) :++ bla :≡ ((bla :++ bla) :++ bla) :++ bla)

-- ASSOCIATIVITY FOR FORMULAS OF SIZE 5
------------------------------------------------------------------------

xs++xs++[xs++xs]++xs≡xs++xs++xs++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ bs ++ (cs ++ ds) ++ es ≡ as ++ bs ++ cs ++ ds ++ es
xs++xs++[xs++xs]++xs≡xs++xs++xs++xs++xs = list-solve
  (bla :++ bla :++ (bla :++ bla) :++ bla :≡ bla :++ bla :++ bla :++ bla :++ bla)

xs++[xs++xs]++xs++xs≡xs++xs++xs++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ (bs ++ cs) ++ ds ++ es ≡ as ++ bs ++ cs ++ ds ++ es
xs++[xs++xs]++xs++xs≡xs++xs++xs++xs++xs = list-solve
  (bla :++ (bla :++ bla) :++ bla :++ bla :≡ bla :++ bla :++ bla :++ bla :++ bla)

xs++[xs++xs++xs]++xs≡xs++xs++xs++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ (bs ++ cs ++ ds) ++ es ≡ as ++ bs ++ cs ++ ds ++ es
xs++[xs++xs++xs]++xs≡xs++xs++xs++xs++xs = list-solve
  (bla :++ (bla :++ bla :++ bla) :++ bla :≡ bla :++ bla :++ bla :++ bla :++ bla)

xs++[[xs++xs]++xs]++xs≡xs++xs++xs++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ ((bs ++ cs) ++ ds) ++ es ≡ as ++ bs ++ cs ++ ds ++ es
xs++[[xs++xs]++xs]++xs≡xs++xs++xs++xs++xs = list-solve
  (bla :++ ((bla :++ bla) :++ bla) :++ bla :≡ bla :++ bla :++ bla :++ bla :++ bla)

[xs++xs]++xs++xs++xs≡xs++xs++xs++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs) ++ cs ++ ds ++ es ≡ as ++ bs ++ cs ++ ds ++ es
[xs++xs]++xs++xs++xs≡xs++xs++xs++xs++xs = list-solve
  ((bla :++ bla) :++ bla :++ bla :++ bla :≡ bla :++ bla :++ bla :++ bla :++ bla)

[xs++xs]++[xs++xs]++xs≡xs++xs++xs++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs) ++ (cs ++ ds) ++ es ≡ as ++ bs ++ cs ++ ds ++ es
[xs++xs]++[xs++xs]++xs≡xs++xs++xs++xs++xs = list-solve
  ((bla :++ bla) :++ (bla :++ bla) :++ bla :≡ bla :++ bla :++ bla :++ bla :++ bla)

[xs++xs++xs]++xs++xs≡xs++xs++xs++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs ++ cs) ++ ds ++ es ≡ as ++ bs ++ cs ++ ds ++ es
[xs++xs++xs]++xs++xs≡xs++xs++xs++xs++xs = list-solve
  ((bla :++ bla :++ bla) :++ bla :++ bla :≡ bla :++ bla :++ bla :++ bla :++ bla)

[[xs++xs]++xs]++xs++xs≡xs++xs++xs++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs) ++ cs) ++ ds ++ es ≡ as ++ bs ++ cs ++ ds ++ es
[[xs++xs]++xs]++xs++xs≡xs++xs++xs++xs++xs = list-solve
  (((bla :++ bla) :++ bla) :++ bla :++ bla :≡ bla :++ bla :++ bla :++ bla :++ bla)

[xs++xs++xs++xs]++xs≡xs++xs++xs++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs ++ cs ++ ds) ++ es ≡ as ++ bs ++ cs ++ ds ++ es
[xs++xs++xs++xs]++xs≡xs++xs++xs++xs++xs = list-solve
  ((bla :++ bla :++ bla :++ bla) :++ bla :≡ bla :++ bla :++ bla :++ bla :++ bla)

[xs++[xs++xs]++xs]++xs≡xs++xs++xs++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ (bs ++ cs) ++ ds) ++ es ≡ as ++ bs ++ cs ++ ds ++ es
[xs++[xs++xs]++xs]++xs≡xs++xs++xs++xs++xs = list-solve
  ((bla :++ (bla :++ bla) :++ bla) :++ bla :≡ bla :++ bla :++ bla :++ bla :++ bla)

[[xs++xs]++xs++xs]++xs≡xs++xs++xs++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs) ++ cs ++ ds) ++ es ≡ as ++ bs ++ cs ++ ds ++ es
[[xs++xs]++xs++xs]++xs≡xs++xs++xs++xs++xs = list-solve
  (((bla :++ bla) :++ bla :++ bla) :++ bla :≡ bla :++ bla :++ bla :++ bla :++ bla)

[[xs++xs++xs]++xs]++xs≡xs++xs++xs++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs ++ cs) ++ ds) ++ es ≡ as ++ bs ++ cs ++ ds ++ es
[[xs++xs++xs]++xs]++xs≡xs++xs++xs++xs++xs = list-solve
  (((bla :++ bla :++ bla) :++ bla) :++ bla :≡ bla :++ bla :++ bla :++ bla :++ bla)

[[[xs++xs]++xs]++xs]++xs≡xs++xs++xs++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (((as ++ bs) ++ cs) ++ ds) ++ es ≡ as ++ bs ++ cs ++ ds ++ es
[[[xs++xs]++xs]++xs]++xs≡xs++xs++xs++xs++xs = list-solve
  ((((bla :++ bla) :++ bla) :++ bla) :++ bla :≡ bla :++ bla :++ bla :++ bla :++ bla)

xs++xs++xs++xs++xs≡xs++xs++[xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ bs ++ cs ++ ds ++ es ≡ as ++ bs ++ (cs ++ ds) ++ es
xs++xs++xs++xs++xs≡xs++xs++[xs++xs]++xs = list-solve
  (bla :++ bla :++ bla :++ bla :++ bla :≡ bla :++ bla :++ (bla :++ bla) :++ bla)

xs++[xs++xs]++xs++xs≡xs++xs++[xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ (bs ++ cs) ++ ds ++ es ≡ as ++ bs ++ (cs ++ ds) ++ es
xs++[xs++xs]++xs++xs≡xs++xs++[xs++xs]++xs = list-solve
  (bla :++ (bla :++ bla) :++ bla :++ bla :≡ bla :++ bla :++ (bla :++ bla) :++ bla)

xs++[xs++xs++xs]++xs≡xs++xs++[xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ (bs ++ cs ++ ds) ++ es ≡ as ++ bs ++ (cs ++ ds) ++ es
xs++[xs++xs++xs]++xs≡xs++xs++[xs++xs]++xs = list-solve
  (bla :++ (bla :++ bla :++ bla) :++ bla :≡ bla :++ bla :++ (bla :++ bla) :++ bla)

xs++[[xs++xs]++xs]++xs≡xs++xs++[xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ ((bs ++ cs) ++ ds) ++ es ≡ as ++ bs ++ (cs ++ ds) ++ es
xs++[[xs++xs]++xs]++xs≡xs++xs++[xs++xs]++xs = list-solve
  (bla :++ ((bla :++ bla) :++ bla) :++ bla :≡ bla :++ bla :++ (bla :++ bla) :++ bla)

[xs++xs]++xs++xs++xs≡xs++xs++[xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs) ++ cs ++ ds ++ es ≡ as ++ bs ++ (cs ++ ds) ++ es
[xs++xs]++xs++xs++xs≡xs++xs++[xs++xs]++xs = list-solve
  ((bla :++ bla) :++ bla :++ bla :++ bla :≡ bla :++ bla :++ (bla :++ bla) :++ bla)

[xs++xs]++[xs++xs]++xs≡xs++xs++[xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs) ++ (cs ++ ds) ++ es ≡ as ++ bs ++ (cs ++ ds) ++ es
[xs++xs]++[xs++xs]++xs≡xs++xs++[xs++xs]++xs = list-solve
  ((bla :++ bla) :++ (bla :++ bla) :++ bla :≡ bla :++ bla :++ (bla :++ bla) :++ bla)

[xs++xs++xs]++xs++xs≡xs++xs++[xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs ++ cs) ++ ds ++ es ≡ as ++ bs ++ (cs ++ ds) ++ es
[xs++xs++xs]++xs++xs≡xs++xs++[xs++xs]++xs = list-solve
  ((bla :++ bla :++ bla) :++ bla :++ bla :≡ bla :++ bla :++ (bla :++ bla) :++ bla)

[[xs++xs]++xs]++xs++xs≡xs++xs++[xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs) ++ cs) ++ ds ++ es ≡ as ++ bs ++ (cs ++ ds) ++ es
[[xs++xs]++xs]++xs++xs≡xs++xs++[xs++xs]++xs = list-solve
  (((bla :++ bla) :++ bla) :++ bla :++ bla :≡ bla :++ bla :++ (bla :++ bla) :++ bla)

[xs++xs++xs++xs]++xs≡xs++xs++[xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs ++ cs ++ ds) ++ es ≡ as ++ bs ++ (cs ++ ds) ++ es
[xs++xs++xs++xs]++xs≡xs++xs++[xs++xs]++xs = list-solve
  ((bla :++ bla :++ bla :++ bla) :++ bla :≡ bla :++ bla :++ (bla :++ bla) :++ bla)

[xs++[xs++xs]++xs]++xs≡xs++xs++[xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ (bs ++ cs) ++ ds) ++ es ≡ as ++ bs ++ (cs ++ ds) ++ es
[xs++[xs++xs]++xs]++xs≡xs++xs++[xs++xs]++xs = list-solve
  ((bla :++ (bla :++ bla) :++ bla) :++ bla :≡ bla :++ bla :++ (bla :++ bla) :++ bla)

[[xs++xs]++xs++xs]++xs≡xs++xs++[xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs) ++ cs ++ ds) ++ es ≡ as ++ bs ++ (cs ++ ds) ++ es
[[xs++xs]++xs++xs]++xs≡xs++xs++[xs++xs]++xs = list-solve
  (((bla :++ bla) :++ bla :++ bla) :++ bla :≡ bla :++ bla :++ (bla :++ bla) :++ bla)

[[xs++xs++xs]++xs]++xs≡xs++xs++[xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs ++ cs) ++ ds) ++ es ≡ as ++ bs ++ (cs ++ ds) ++ es
[[xs++xs++xs]++xs]++xs≡xs++xs++[xs++xs]++xs = list-solve
  (((bla :++ bla :++ bla) :++ bla) :++ bla :≡ bla :++ bla :++ (bla :++ bla) :++ bla)

[[[xs++xs]++xs]++xs]++xs≡xs++xs++[xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (((as ++ bs) ++ cs) ++ ds) ++ es ≡ as ++ bs ++ (cs ++ ds) ++ es
[[[xs++xs]++xs]++xs]++xs≡xs++xs++[xs++xs]++xs = list-solve
  ((((bla :++ bla) :++ bla) :++ bla) :++ bla :≡ bla :++ bla :++ (bla :++ bla) :++ bla)

xs++xs++xs++xs++xs≡xs++[xs++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ bs ++ cs ++ ds ++ es ≡ as ++ (bs ++ cs) ++ ds ++ es
xs++xs++xs++xs++xs≡xs++[xs++xs]++xs++xs = list-solve
  (bla :++ bla :++ bla :++ bla :++ bla :≡ bla :++ (bla :++ bla) :++ bla :++ bla)

xs++xs++[xs++xs]++xs≡xs++[xs++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ bs ++ (cs ++ ds) ++ es ≡ as ++ (bs ++ cs) ++ ds ++ es
xs++xs++[xs++xs]++xs≡xs++[xs++xs]++xs++xs = list-solve
  (bla :++ bla :++ (bla :++ bla) :++ bla :≡ bla :++ (bla :++ bla) :++ bla :++ bla)

xs++[xs++xs++xs]++xs≡xs++[xs++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ (bs ++ cs ++ ds) ++ es ≡ as ++ (bs ++ cs) ++ ds ++ es
xs++[xs++xs++xs]++xs≡xs++[xs++xs]++xs++xs = list-solve
  (bla :++ (bla :++ bla :++ bla) :++ bla :≡ bla :++ (bla :++ bla) :++ bla :++ bla)

xs++[[xs++xs]++xs]++xs≡xs++[xs++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ ((bs ++ cs) ++ ds) ++ es ≡ as ++ (bs ++ cs) ++ ds ++ es
xs++[[xs++xs]++xs]++xs≡xs++[xs++xs]++xs++xs = list-solve
  (bla :++ ((bla :++ bla) :++ bla) :++ bla :≡ bla :++ (bla :++ bla) :++ bla :++ bla)

[xs++xs]++xs++xs++xs≡xs++[xs++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs) ++ cs ++ ds ++ es ≡ as ++ (bs ++ cs) ++ ds ++ es
[xs++xs]++xs++xs++xs≡xs++[xs++xs]++xs++xs = list-solve
  ((bla :++ bla) :++ bla :++ bla :++ bla :≡ bla :++ (bla :++ bla) :++ bla :++ bla)

[xs++xs]++[xs++xs]++xs≡xs++[xs++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs) ++ (cs ++ ds) ++ es ≡ as ++ (bs ++ cs) ++ ds ++ es
[xs++xs]++[xs++xs]++xs≡xs++[xs++xs]++xs++xs = list-solve
  ((bla :++ bla) :++ (bla :++ bla) :++ bla :≡ bla :++ (bla :++ bla) :++ bla :++ bla)

[xs++xs++xs]++xs++xs≡xs++[xs++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs ++ cs) ++ ds ++ es ≡ as ++ (bs ++ cs) ++ ds ++ es
[xs++xs++xs]++xs++xs≡xs++[xs++xs]++xs++xs = list-solve
  ((bla :++ bla :++ bla) :++ bla :++ bla :≡ bla :++ (bla :++ bla) :++ bla :++ bla)

[[xs++xs]++xs]++xs++xs≡xs++[xs++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs) ++ cs) ++ ds ++ es ≡ as ++ (bs ++ cs) ++ ds ++ es
[[xs++xs]++xs]++xs++xs≡xs++[xs++xs]++xs++xs = list-solve
  (((bla :++ bla) :++ bla) :++ bla :++ bla :≡ bla :++ (bla :++ bla) :++ bla :++ bla)

[xs++xs++xs++xs]++xs≡xs++[xs++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs ++ cs ++ ds) ++ es ≡ as ++ (bs ++ cs) ++ ds ++ es
[xs++xs++xs++xs]++xs≡xs++[xs++xs]++xs++xs = list-solve
  ((bla :++ bla :++ bla :++ bla) :++ bla :≡ bla :++ (bla :++ bla) :++ bla :++ bla)

[xs++[xs++xs]++xs]++xs≡xs++[xs++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ (bs ++ cs) ++ ds) ++ es ≡ as ++ (bs ++ cs) ++ ds ++ es
[xs++[xs++xs]++xs]++xs≡xs++[xs++xs]++xs++xs = list-solve
  ((bla :++ (bla :++ bla) :++ bla) :++ bla :≡ bla :++ (bla :++ bla) :++ bla :++ bla)

[[xs++xs]++xs++xs]++xs≡xs++[xs++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs) ++ cs ++ ds) ++ es ≡ as ++ (bs ++ cs) ++ ds ++ es
[[xs++xs]++xs++xs]++xs≡xs++[xs++xs]++xs++xs = list-solve
  (((bla :++ bla) :++ bla :++ bla) :++ bla :≡ bla :++ (bla :++ bla) :++ bla :++ bla)

[[xs++xs++xs]++xs]++xs≡xs++[xs++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs ++ cs) ++ ds) ++ es ≡ as ++ (bs ++ cs) ++ ds ++ es
[[xs++xs++xs]++xs]++xs≡xs++[xs++xs]++xs++xs = list-solve
  (((bla :++ bla :++ bla) :++ bla) :++ bla :≡ bla :++ (bla :++ bla) :++ bla :++ bla)

[[[xs++xs]++xs]++xs]++xs≡xs++[xs++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (((as ++ bs) ++ cs) ++ ds) ++ es ≡ as ++ (bs ++ cs) ++ ds ++ es
[[[xs++xs]++xs]++xs]++xs≡xs++[xs++xs]++xs++xs = list-solve
  ((((bla :++ bla) :++ bla) :++ bla) :++ bla :≡ bla :++ (bla :++ bla) :++ bla :++ bla)

xs++xs++xs++xs++xs≡xs++[xs++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ bs ++ cs ++ ds ++ es ≡ as ++ (bs ++ cs ++ ds) ++ es
xs++xs++xs++xs++xs≡xs++[xs++xs++xs]++xs = list-solve
  (bla :++ bla :++ bla :++ bla :++ bla :≡ bla :++ (bla :++ bla :++ bla) :++ bla)

xs++xs++[xs++xs]++xs≡xs++[xs++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ bs ++ (cs ++ ds) ++ es ≡ as ++ (bs ++ cs ++ ds) ++ es
xs++xs++[xs++xs]++xs≡xs++[xs++xs++xs]++xs = list-solve
  (bla :++ bla :++ (bla :++ bla) :++ bla :≡ bla :++ (bla :++ bla :++ bla) :++ bla)

xs++[xs++xs]++xs++xs≡xs++[xs++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ (bs ++ cs) ++ ds ++ es ≡ as ++ (bs ++ cs ++ ds) ++ es
xs++[xs++xs]++xs++xs≡xs++[xs++xs++xs]++xs = list-solve
  (bla :++ (bla :++ bla) :++ bla :++ bla :≡ bla :++ (bla :++ bla :++ bla) :++ bla)

xs++[[xs++xs]++xs]++xs≡xs++[xs++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ ((bs ++ cs) ++ ds) ++ es ≡ as ++ (bs ++ cs ++ ds) ++ es
xs++[[xs++xs]++xs]++xs≡xs++[xs++xs++xs]++xs = list-solve
  (bla :++ ((bla :++ bla) :++ bla) :++ bla :≡ bla :++ (bla :++ bla :++ bla) :++ bla)

[xs++xs]++xs++xs++xs≡xs++[xs++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs) ++ cs ++ ds ++ es ≡ as ++ (bs ++ cs ++ ds) ++ es
[xs++xs]++xs++xs++xs≡xs++[xs++xs++xs]++xs = list-solve
  ((bla :++ bla) :++ bla :++ bla :++ bla :≡ bla :++ (bla :++ bla :++ bla) :++ bla)

[xs++xs]++[xs++xs]++xs≡xs++[xs++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs) ++ (cs ++ ds) ++ es ≡ as ++ (bs ++ cs ++ ds) ++ es
[xs++xs]++[xs++xs]++xs≡xs++[xs++xs++xs]++xs = list-solve
  ((bla :++ bla) :++ (bla :++ bla) :++ bla :≡ bla :++ (bla :++ bla :++ bla) :++ bla)

[xs++xs++xs]++xs++xs≡xs++[xs++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs ++ cs) ++ ds ++ es ≡ as ++ (bs ++ cs ++ ds) ++ es
[xs++xs++xs]++xs++xs≡xs++[xs++xs++xs]++xs = list-solve
  ((bla :++ bla :++ bla) :++ bla :++ bla :≡ bla :++ (bla :++ bla :++ bla) :++ bla)

[[xs++xs]++xs]++xs++xs≡xs++[xs++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs) ++ cs) ++ ds ++ es ≡ as ++ (bs ++ cs ++ ds) ++ es
[[xs++xs]++xs]++xs++xs≡xs++[xs++xs++xs]++xs = list-solve
  (((bla :++ bla) :++ bla) :++ bla :++ bla :≡ bla :++ (bla :++ bla :++ bla) :++ bla)

[xs++xs++xs++xs]++xs≡xs++[xs++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs ++ cs ++ ds) ++ es ≡ as ++ (bs ++ cs ++ ds) ++ es
[xs++xs++xs++xs]++xs≡xs++[xs++xs++xs]++xs = list-solve
  ((bla :++ bla :++ bla :++ bla) :++ bla :≡ bla :++ (bla :++ bla :++ bla) :++ bla)

[xs++[xs++xs]++xs]++xs≡xs++[xs++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ (bs ++ cs) ++ ds) ++ es ≡ as ++ (bs ++ cs ++ ds) ++ es
[xs++[xs++xs]++xs]++xs≡xs++[xs++xs++xs]++xs = list-solve
  ((bla :++ (bla :++ bla) :++ bla) :++ bla :≡ bla :++ (bla :++ bla :++ bla) :++ bla)

[[xs++xs]++xs++xs]++xs≡xs++[xs++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs) ++ cs ++ ds) ++ es ≡ as ++ (bs ++ cs ++ ds) ++ es
[[xs++xs]++xs++xs]++xs≡xs++[xs++xs++xs]++xs = list-solve
  (((bla :++ bla) :++ bla :++ bla) :++ bla :≡ bla :++ (bla :++ bla :++ bla) :++ bla)

[[xs++xs++xs]++xs]++xs≡xs++[xs++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs ++ cs) ++ ds) ++ es ≡ as ++ (bs ++ cs ++ ds) ++ es
[[xs++xs++xs]++xs]++xs≡xs++[xs++xs++xs]++xs = list-solve
  (((bla :++ bla :++ bla) :++ bla) :++ bla :≡ bla :++ (bla :++ bla :++ bla) :++ bla)

[[[xs++xs]++xs]++xs]++xs≡xs++[xs++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (((as ++ bs) ++ cs) ++ ds) ++ es ≡ as ++ (bs ++ cs ++ ds) ++ es
[[[xs++xs]++xs]++xs]++xs≡xs++[xs++xs++xs]++xs = list-solve
  ((((bla :++ bla) :++ bla) :++ bla) :++ bla :≡ bla :++ (bla :++ bla :++ bla) :++ bla)

xs++xs++xs++xs++xs≡xs++[[xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ bs ++ cs ++ ds ++ es ≡ as ++ ((bs ++ cs) ++ ds) ++ es
xs++xs++xs++xs++xs≡xs++[[xs++xs]++xs]++xs = list-solve
  (bla :++ bla :++ bla :++ bla :++ bla :≡ bla :++ ((bla :++ bla) :++ bla) :++ bla)

xs++xs++[xs++xs]++xs≡xs++[[xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ bs ++ (cs ++ ds) ++ es ≡ as ++ ((bs ++ cs) ++ ds) ++ es
xs++xs++[xs++xs]++xs≡xs++[[xs++xs]++xs]++xs = list-solve
  (bla :++ bla :++ (bla :++ bla) :++ bla :≡ bla :++ ((bla :++ bla) :++ bla) :++ bla)

xs++[xs++xs]++xs++xs≡xs++[[xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ (bs ++ cs) ++ ds ++ es ≡ as ++ ((bs ++ cs) ++ ds) ++ es
xs++[xs++xs]++xs++xs≡xs++[[xs++xs]++xs]++xs = list-solve
  (bla :++ (bla :++ bla) :++ bla :++ bla :≡ bla :++ ((bla :++ bla) :++ bla) :++ bla)

xs++[xs++xs++xs]++xs≡xs++[[xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ (bs ++ cs ++ ds) ++ es ≡ as ++ ((bs ++ cs) ++ ds) ++ es
xs++[xs++xs++xs]++xs≡xs++[[xs++xs]++xs]++xs = list-solve
  (bla :++ (bla :++ bla :++ bla) :++ bla :≡ bla :++ ((bla :++ bla) :++ bla) :++ bla)

[xs++xs]++xs++xs++xs≡xs++[[xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs) ++ cs ++ ds ++ es ≡ as ++ ((bs ++ cs) ++ ds) ++ es
[xs++xs]++xs++xs++xs≡xs++[[xs++xs]++xs]++xs = list-solve
  ((bla :++ bla) :++ bla :++ bla :++ bla :≡ bla :++ ((bla :++ bla) :++ bla) :++ bla)

[xs++xs]++[xs++xs]++xs≡xs++[[xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs) ++ (cs ++ ds) ++ es ≡ as ++ ((bs ++ cs) ++ ds) ++ es
[xs++xs]++[xs++xs]++xs≡xs++[[xs++xs]++xs]++xs = list-solve
  ((bla :++ bla) :++ (bla :++ bla) :++ bla :≡ bla :++ ((bla :++ bla) :++ bla) :++ bla)

[xs++xs++xs]++xs++xs≡xs++[[xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs ++ cs) ++ ds ++ es ≡ as ++ ((bs ++ cs) ++ ds) ++ es
[xs++xs++xs]++xs++xs≡xs++[[xs++xs]++xs]++xs = list-solve
  ((bla :++ bla :++ bla) :++ bla :++ bla :≡ bla :++ ((bla :++ bla) :++ bla) :++ bla)

[[xs++xs]++xs]++xs++xs≡xs++[[xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs) ++ cs) ++ ds ++ es ≡ as ++ ((bs ++ cs) ++ ds) ++ es
[[xs++xs]++xs]++xs++xs≡xs++[[xs++xs]++xs]++xs = list-solve
  (((bla :++ bla) :++ bla) :++ bla :++ bla :≡ bla :++ ((bla :++ bla) :++ bla) :++ bla)

[xs++xs++xs++xs]++xs≡xs++[[xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs ++ cs ++ ds) ++ es ≡ as ++ ((bs ++ cs) ++ ds) ++ es
[xs++xs++xs++xs]++xs≡xs++[[xs++xs]++xs]++xs = list-solve
  ((bla :++ bla :++ bla :++ bla) :++ bla :≡ bla :++ ((bla :++ bla) :++ bla) :++ bla)

[xs++[xs++xs]++xs]++xs≡xs++[[xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ (bs ++ cs) ++ ds) ++ es ≡ as ++ ((bs ++ cs) ++ ds) ++ es
[xs++[xs++xs]++xs]++xs≡xs++[[xs++xs]++xs]++xs = list-solve
  ((bla :++ (bla :++ bla) :++ bla) :++ bla :≡ bla :++ ((bla :++ bla) :++ bla) :++ bla)

[[xs++xs]++xs++xs]++xs≡xs++[[xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs) ++ cs ++ ds) ++ es ≡ as ++ ((bs ++ cs) ++ ds) ++ es
[[xs++xs]++xs++xs]++xs≡xs++[[xs++xs]++xs]++xs = list-solve
  (((bla :++ bla) :++ bla :++ bla) :++ bla :≡ bla :++ ((bla :++ bla) :++ bla) :++ bla)

[[xs++xs++xs]++xs]++xs≡xs++[[xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs ++ cs) ++ ds) ++ es ≡ as ++ ((bs ++ cs) ++ ds) ++ es
[[xs++xs++xs]++xs]++xs≡xs++[[xs++xs]++xs]++xs = list-solve
  (((bla :++ bla :++ bla) :++ bla) :++ bla :≡ bla :++ ((bla :++ bla) :++ bla) :++ bla)

[[[xs++xs]++xs]++xs]++xs≡xs++[[xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (((as ++ bs) ++ cs) ++ ds) ++ es ≡ as ++ ((bs ++ cs) ++ ds) ++ es
[[[xs++xs]++xs]++xs]++xs≡xs++[[xs++xs]++xs]++xs = list-solve
  ((((bla :++ bla) :++ bla) :++ bla) :++ bla :≡ bla :++ ((bla :++ bla) :++ bla) :++ bla)

xs++xs++xs++xs++xs≡[xs++xs]++xs++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ bs ++ cs ++ ds ++ es ≡ (as ++ bs) ++ cs ++ ds ++ es
xs++xs++xs++xs++xs≡[xs++xs]++xs++xs++xs = list-solve
  (bla :++ bla :++ bla :++ bla :++ bla :≡ (bla :++ bla) :++ bla :++ bla :++ bla)

xs++xs++[xs++xs]++xs≡[xs++xs]++xs++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ bs ++ (cs ++ ds) ++ es ≡ (as ++ bs) ++ cs ++ ds ++ es
xs++xs++[xs++xs]++xs≡[xs++xs]++xs++xs++xs = list-solve
  (bla :++ bla :++ (bla :++ bla) :++ bla :≡ (bla :++ bla) :++ bla :++ bla :++ bla)

xs++[xs++xs]++xs++xs≡[xs++xs]++xs++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ (bs ++ cs) ++ ds ++ es ≡ (as ++ bs) ++ cs ++ ds ++ es
xs++[xs++xs]++xs++xs≡[xs++xs]++xs++xs++xs = list-solve
  (bla :++ (bla :++ bla) :++ bla :++ bla :≡ (bla :++ bla) :++ bla :++ bla :++ bla)

xs++[xs++xs++xs]++xs≡[xs++xs]++xs++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ (bs ++ cs ++ ds) ++ es ≡ (as ++ bs) ++ cs ++ ds ++ es
xs++[xs++xs++xs]++xs≡[xs++xs]++xs++xs++xs = list-solve
  (bla :++ (bla :++ bla :++ bla) :++ bla :≡ (bla :++ bla) :++ bla :++ bla :++ bla)

xs++[[xs++xs]++xs]++xs≡[xs++xs]++xs++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ ((bs ++ cs) ++ ds) ++ es ≡ (as ++ bs) ++ cs ++ ds ++ es
xs++[[xs++xs]++xs]++xs≡[xs++xs]++xs++xs++xs = list-solve
  (bla :++ ((bla :++ bla) :++ bla) :++ bla :≡ (bla :++ bla) :++ bla :++ bla :++ bla)

[xs++xs]++[xs++xs]++xs≡[xs++xs]++xs++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs) ++ (cs ++ ds) ++ es ≡ (as ++ bs) ++ cs ++ ds ++ es
[xs++xs]++[xs++xs]++xs≡[xs++xs]++xs++xs++xs = list-solve
  ((bla :++ bla) :++ (bla :++ bla) :++ bla :≡ (bla :++ bla) :++ bla :++ bla :++ bla)

[xs++xs++xs]++xs++xs≡[xs++xs]++xs++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs ++ cs) ++ ds ++ es ≡ (as ++ bs) ++ cs ++ ds ++ es
[xs++xs++xs]++xs++xs≡[xs++xs]++xs++xs++xs = list-solve
  ((bla :++ bla :++ bla) :++ bla :++ bla :≡ (bla :++ bla) :++ bla :++ bla :++ bla)

[[xs++xs]++xs]++xs++xs≡[xs++xs]++xs++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs) ++ cs) ++ ds ++ es ≡ (as ++ bs) ++ cs ++ ds ++ es
[[xs++xs]++xs]++xs++xs≡[xs++xs]++xs++xs++xs = list-solve
  (((bla :++ bla) :++ bla) :++ bla :++ bla :≡ (bla :++ bla) :++ bla :++ bla :++ bla)

[xs++xs++xs++xs]++xs≡[xs++xs]++xs++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs ++ cs ++ ds) ++ es ≡ (as ++ bs) ++ cs ++ ds ++ es
[xs++xs++xs++xs]++xs≡[xs++xs]++xs++xs++xs = list-solve
  ((bla :++ bla :++ bla :++ bla) :++ bla :≡ (bla :++ bla) :++ bla :++ bla :++ bla)

[xs++[xs++xs]++xs]++xs≡[xs++xs]++xs++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ (bs ++ cs) ++ ds) ++ es ≡ (as ++ bs) ++ cs ++ ds ++ es
[xs++[xs++xs]++xs]++xs≡[xs++xs]++xs++xs++xs = list-solve
  ((bla :++ (bla :++ bla) :++ bla) :++ bla :≡ (bla :++ bla) :++ bla :++ bla :++ bla)

[[xs++xs]++xs++xs]++xs≡[xs++xs]++xs++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs) ++ cs ++ ds) ++ es ≡ (as ++ bs) ++ cs ++ ds ++ es
[[xs++xs]++xs++xs]++xs≡[xs++xs]++xs++xs++xs = list-solve
  (((bla :++ bla) :++ bla :++ bla) :++ bla :≡ (bla :++ bla) :++ bla :++ bla :++ bla)

[[xs++xs++xs]++xs]++xs≡[xs++xs]++xs++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs ++ cs) ++ ds) ++ es ≡ (as ++ bs) ++ cs ++ ds ++ es
[[xs++xs++xs]++xs]++xs≡[xs++xs]++xs++xs++xs = list-solve
  (((bla :++ bla :++ bla) :++ bla) :++ bla :≡ (bla :++ bla) :++ bla :++ bla :++ bla)

[[[xs++xs]++xs]++xs]++xs≡[xs++xs]++xs++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (((as ++ bs) ++ cs) ++ ds) ++ es ≡ (as ++ bs) ++ cs ++ ds ++ es
[[[xs++xs]++xs]++xs]++xs≡[xs++xs]++xs++xs++xs = list-solve
  ((((bla :++ bla) :++ bla) :++ bla) :++ bla :≡ (bla :++ bla) :++ bla :++ bla :++ bla)

xs++xs++xs++xs++xs≡[xs++xs]++[xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ bs ++ cs ++ ds ++ es ≡ (as ++ bs) ++ (cs ++ ds) ++ es
xs++xs++xs++xs++xs≡[xs++xs]++[xs++xs]++xs = list-solve
  (bla :++ bla :++ bla :++ bla :++ bla :≡ (bla :++ bla) :++ (bla :++ bla) :++ bla)

xs++xs++[xs++xs]++xs≡[xs++xs]++[xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ bs ++ (cs ++ ds) ++ es ≡ (as ++ bs) ++ (cs ++ ds) ++ es
xs++xs++[xs++xs]++xs≡[xs++xs]++[xs++xs]++xs = list-solve
  (bla :++ bla :++ (bla :++ bla) :++ bla :≡ (bla :++ bla) :++ (bla :++ bla) :++ bla)

xs++[xs++xs]++xs++xs≡[xs++xs]++[xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ (bs ++ cs) ++ ds ++ es ≡ (as ++ bs) ++ (cs ++ ds) ++ es
xs++[xs++xs]++xs++xs≡[xs++xs]++[xs++xs]++xs = list-solve
  (bla :++ (bla :++ bla) :++ bla :++ bla :≡ (bla :++ bla) :++ (bla :++ bla) :++ bla)

xs++[xs++xs++xs]++xs≡[xs++xs]++[xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ (bs ++ cs ++ ds) ++ es ≡ (as ++ bs) ++ (cs ++ ds) ++ es
xs++[xs++xs++xs]++xs≡[xs++xs]++[xs++xs]++xs = list-solve
  (bla :++ (bla :++ bla :++ bla) :++ bla :≡ (bla :++ bla) :++ (bla :++ bla) :++ bla)

xs++[[xs++xs]++xs]++xs≡[xs++xs]++[xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ ((bs ++ cs) ++ ds) ++ es ≡ (as ++ bs) ++ (cs ++ ds) ++ es
xs++[[xs++xs]++xs]++xs≡[xs++xs]++[xs++xs]++xs = list-solve
  (bla :++ ((bla :++ bla) :++ bla) :++ bla :≡ (bla :++ bla) :++ (bla :++ bla) :++ bla)

[xs++xs]++xs++xs++xs≡[xs++xs]++[xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs) ++ cs ++ ds ++ es ≡ (as ++ bs) ++ (cs ++ ds) ++ es
[xs++xs]++xs++xs++xs≡[xs++xs]++[xs++xs]++xs = list-solve
  ((bla :++ bla) :++ bla :++ bla :++ bla :≡ (bla :++ bla) :++ (bla :++ bla) :++ bla)

[xs++xs++xs]++xs++xs≡[xs++xs]++[xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs ++ cs) ++ ds ++ es ≡ (as ++ bs) ++ (cs ++ ds) ++ es
[xs++xs++xs]++xs++xs≡[xs++xs]++[xs++xs]++xs = list-solve
  ((bla :++ bla :++ bla) :++ bla :++ bla :≡ (bla :++ bla) :++ (bla :++ bla) :++ bla)

[[xs++xs]++xs]++xs++xs≡[xs++xs]++[xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs) ++ cs) ++ ds ++ es ≡ (as ++ bs) ++ (cs ++ ds) ++ es
[[xs++xs]++xs]++xs++xs≡[xs++xs]++[xs++xs]++xs = list-solve
  (((bla :++ bla) :++ bla) :++ bla :++ bla :≡ (bla :++ bla) :++ (bla :++ bla) :++ bla)

[xs++xs++xs++xs]++xs≡[xs++xs]++[xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs ++ cs ++ ds) ++ es ≡ (as ++ bs) ++ (cs ++ ds) ++ es
[xs++xs++xs++xs]++xs≡[xs++xs]++[xs++xs]++xs = list-solve
  ((bla :++ bla :++ bla :++ bla) :++ bla :≡ (bla :++ bla) :++ (bla :++ bla) :++ bla)

[xs++[xs++xs]++xs]++xs≡[xs++xs]++[xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ (bs ++ cs) ++ ds) ++ es ≡ (as ++ bs) ++ (cs ++ ds) ++ es
[xs++[xs++xs]++xs]++xs≡[xs++xs]++[xs++xs]++xs = list-solve
  ((bla :++ (bla :++ bla) :++ bla) :++ bla :≡ (bla :++ bla) :++ (bla :++ bla) :++ bla)

[[xs++xs]++xs++xs]++xs≡[xs++xs]++[xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs) ++ cs ++ ds) ++ es ≡ (as ++ bs) ++ (cs ++ ds) ++ es
[[xs++xs]++xs++xs]++xs≡[xs++xs]++[xs++xs]++xs = list-solve
  (((bla :++ bla) :++ bla :++ bla) :++ bla :≡ (bla :++ bla) :++ (bla :++ bla) :++ bla)

[[xs++xs++xs]++xs]++xs≡[xs++xs]++[xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs ++ cs) ++ ds) ++ es ≡ (as ++ bs) ++ (cs ++ ds) ++ es
[[xs++xs++xs]++xs]++xs≡[xs++xs]++[xs++xs]++xs = list-solve
  (((bla :++ bla :++ bla) :++ bla) :++ bla :≡ (bla :++ bla) :++ (bla :++ bla) :++ bla)

[[[xs++xs]++xs]++xs]++xs≡[xs++xs]++[xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (((as ++ bs) ++ cs) ++ ds) ++ es ≡ (as ++ bs) ++ (cs ++ ds) ++ es
[[[xs++xs]++xs]++xs]++xs≡[xs++xs]++[xs++xs]++xs = list-solve
  ((((bla :++ bla) :++ bla) :++ bla) :++ bla :≡ (bla :++ bla) :++ (bla :++ bla) :++ bla)

xs++xs++xs++xs++xs≡[xs++xs++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ bs ++ cs ++ ds ++ es ≡ (as ++ bs ++ cs) ++ ds ++ es
xs++xs++xs++xs++xs≡[xs++xs++xs]++xs++xs = list-solve
  (bla :++ bla :++ bla :++ bla :++ bla :≡ (bla :++ bla :++ bla) :++ bla :++ bla)

xs++xs++[xs++xs]++xs≡[xs++xs++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ bs ++ (cs ++ ds) ++ es ≡ (as ++ bs ++ cs) ++ ds ++ es
xs++xs++[xs++xs]++xs≡[xs++xs++xs]++xs++xs = list-solve
  (bla :++ bla :++ (bla :++ bla) :++ bla :≡ (bla :++ bla :++ bla) :++ bla :++ bla)

xs++[xs++xs]++xs++xs≡[xs++xs++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ (bs ++ cs) ++ ds ++ es ≡ (as ++ bs ++ cs) ++ ds ++ es
xs++[xs++xs]++xs++xs≡[xs++xs++xs]++xs++xs = list-solve
  (bla :++ (bla :++ bla) :++ bla :++ bla :≡ (bla :++ bla :++ bla) :++ bla :++ bla)

xs++[xs++xs++xs]++xs≡[xs++xs++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ (bs ++ cs ++ ds) ++ es ≡ (as ++ bs ++ cs) ++ ds ++ es
xs++[xs++xs++xs]++xs≡[xs++xs++xs]++xs++xs = list-solve
  (bla :++ (bla :++ bla :++ bla) :++ bla :≡ (bla :++ bla :++ bla) :++ bla :++ bla)

xs++[[xs++xs]++xs]++xs≡[xs++xs++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ ((bs ++ cs) ++ ds) ++ es ≡ (as ++ bs ++ cs) ++ ds ++ es
xs++[[xs++xs]++xs]++xs≡[xs++xs++xs]++xs++xs = list-solve
  (bla :++ ((bla :++ bla) :++ bla) :++ bla :≡ (bla :++ bla :++ bla) :++ bla :++ bla)

[xs++xs]++xs++xs++xs≡[xs++xs++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs) ++ cs ++ ds ++ es ≡ (as ++ bs ++ cs) ++ ds ++ es
[xs++xs]++xs++xs++xs≡[xs++xs++xs]++xs++xs = list-solve
  ((bla :++ bla) :++ bla :++ bla :++ bla :≡ (bla :++ bla :++ bla) :++ bla :++ bla)

[xs++xs]++[xs++xs]++xs≡[xs++xs++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs) ++ (cs ++ ds) ++ es ≡ (as ++ bs ++ cs) ++ ds ++ es
[xs++xs]++[xs++xs]++xs≡[xs++xs++xs]++xs++xs = list-solve
  ((bla :++ bla) :++ (bla :++ bla) :++ bla :≡ (bla :++ bla :++ bla) :++ bla :++ bla)

[[xs++xs]++xs]++xs++xs≡[xs++xs++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs) ++ cs) ++ ds ++ es ≡ (as ++ bs ++ cs) ++ ds ++ es
[[xs++xs]++xs]++xs++xs≡[xs++xs++xs]++xs++xs = list-solve
  (((bla :++ bla) :++ bla) :++ bla :++ bla :≡ (bla :++ bla :++ bla) :++ bla :++ bla)

[xs++xs++xs++xs]++xs≡[xs++xs++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs ++ cs ++ ds) ++ es ≡ (as ++ bs ++ cs) ++ ds ++ es
[xs++xs++xs++xs]++xs≡[xs++xs++xs]++xs++xs = list-solve
  ((bla :++ bla :++ bla :++ bla) :++ bla :≡ (bla :++ bla :++ bla) :++ bla :++ bla)

[xs++[xs++xs]++xs]++xs≡[xs++xs++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ (bs ++ cs) ++ ds) ++ es ≡ (as ++ bs ++ cs) ++ ds ++ es
[xs++[xs++xs]++xs]++xs≡[xs++xs++xs]++xs++xs = list-solve
  ((bla :++ (bla :++ bla) :++ bla) :++ bla :≡ (bla :++ bla :++ bla) :++ bla :++ bla)

[[xs++xs]++xs++xs]++xs≡[xs++xs++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs) ++ cs ++ ds) ++ es ≡ (as ++ bs ++ cs) ++ ds ++ es
[[xs++xs]++xs++xs]++xs≡[xs++xs++xs]++xs++xs = list-solve
  (((bla :++ bla) :++ bla :++ bla) :++ bla :≡ (bla :++ bla :++ bla) :++ bla :++ bla)

[[xs++xs++xs]++xs]++xs≡[xs++xs++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs ++ cs) ++ ds) ++ es ≡ (as ++ bs ++ cs) ++ ds ++ es
[[xs++xs++xs]++xs]++xs≡[xs++xs++xs]++xs++xs = list-solve
  (((bla :++ bla :++ bla) :++ bla) :++ bla :≡ (bla :++ bla :++ bla) :++ bla :++ bla)

[[[xs++xs]++xs]++xs]++xs≡[xs++xs++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (((as ++ bs) ++ cs) ++ ds) ++ es ≡ (as ++ bs ++ cs) ++ ds ++ es
[[[xs++xs]++xs]++xs]++xs≡[xs++xs++xs]++xs++xs = list-solve
  ((((bla :++ bla) :++ bla) :++ bla) :++ bla :≡ (bla :++ bla :++ bla) :++ bla :++ bla)

xs++xs++xs++xs++xs≡[[xs++xs]++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ bs ++ cs ++ ds ++ es ≡ ((as ++ bs) ++ cs) ++ ds ++ es
xs++xs++xs++xs++xs≡[[xs++xs]++xs]++xs++xs = list-solve
  (bla :++ bla :++ bla :++ bla :++ bla :≡ ((bla :++ bla) :++ bla) :++ bla :++ bla)

xs++xs++[xs++xs]++xs≡[[xs++xs]++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ bs ++ (cs ++ ds) ++ es ≡ ((as ++ bs) ++ cs) ++ ds ++ es
xs++xs++[xs++xs]++xs≡[[xs++xs]++xs]++xs++xs = list-solve
  (bla :++ bla :++ (bla :++ bla) :++ bla :≡ ((bla :++ bla) :++ bla) :++ bla :++ bla)

xs++[xs++xs]++xs++xs≡[[xs++xs]++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ (bs ++ cs) ++ ds ++ es ≡ ((as ++ bs) ++ cs) ++ ds ++ es
xs++[xs++xs]++xs++xs≡[[xs++xs]++xs]++xs++xs = list-solve
  (bla :++ (bla :++ bla) :++ bla :++ bla :≡ ((bla :++ bla) :++ bla) :++ bla :++ bla)

xs++[xs++xs++xs]++xs≡[[xs++xs]++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ (bs ++ cs ++ ds) ++ es ≡ ((as ++ bs) ++ cs) ++ ds ++ es
xs++[xs++xs++xs]++xs≡[[xs++xs]++xs]++xs++xs = list-solve
  (bla :++ (bla :++ bla :++ bla) :++ bla :≡ ((bla :++ bla) :++ bla) :++ bla :++ bla)

xs++[[xs++xs]++xs]++xs≡[[xs++xs]++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ ((bs ++ cs) ++ ds) ++ es ≡ ((as ++ bs) ++ cs) ++ ds ++ es
xs++[[xs++xs]++xs]++xs≡[[xs++xs]++xs]++xs++xs = list-solve
  (bla :++ ((bla :++ bla) :++ bla) :++ bla :≡ ((bla :++ bla) :++ bla) :++ bla :++ bla)

[xs++xs]++xs++xs++xs≡[[xs++xs]++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs) ++ cs ++ ds ++ es ≡ ((as ++ bs) ++ cs) ++ ds ++ es
[xs++xs]++xs++xs++xs≡[[xs++xs]++xs]++xs++xs = list-solve
  ((bla :++ bla) :++ bla :++ bla :++ bla :≡ ((bla :++ bla) :++ bla) :++ bla :++ bla)

[xs++xs]++[xs++xs]++xs≡[[xs++xs]++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs) ++ (cs ++ ds) ++ es ≡ ((as ++ bs) ++ cs) ++ ds ++ es
[xs++xs]++[xs++xs]++xs≡[[xs++xs]++xs]++xs++xs = list-solve
  ((bla :++ bla) :++ (bla :++ bla) :++ bla :≡ ((bla :++ bla) :++ bla) :++ bla :++ bla)

[xs++xs++xs]++xs++xs≡[[xs++xs]++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs ++ cs) ++ ds ++ es ≡ ((as ++ bs) ++ cs) ++ ds ++ es
[xs++xs++xs]++xs++xs≡[[xs++xs]++xs]++xs++xs = list-solve
  ((bla :++ bla :++ bla) :++ bla :++ bla :≡ ((bla :++ bla) :++ bla) :++ bla :++ bla)

[xs++xs++xs++xs]++xs≡[[xs++xs]++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs ++ cs ++ ds) ++ es ≡ ((as ++ bs) ++ cs) ++ ds ++ es
[xs++xs++xs++xs]++xs≡[[xs++xs]++xs]++xs++xs = list-solve
  ((bla :++ bla :++ bla :++ bla) :++ bla :≡ ((bla :++ bla) :++ bla) :++ bla :++ bla)

[xs++[xs++xs]++xs]++xs≡[[xs++xs]++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ (bs ++ cs) ++ ds) ++ es ≡ ((as ++ bs) ++ cs) ++ ds ++ es
[xs++[xs++xs]++xs]++xs≡[[xs++xs]++xs]++xs++xs = list-solve
  ((bla :++ (bla :++ bla) :++ bla) :++ bla :≡ ((bla :++ bla) :++ bla) :++ bla :++ bla)

[[xs++xs]++xs++xs]++xs≡[[xs++xs]++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs) ++ cs ++ ds) ++ es ≡ ((as ++ bs) ++ cs) ++ ds ++ es
[[xs++xs]++xs++xs]++xs≡[[xs++xs]++xs]++xs++xs = list-solve
  (((bla :++ bla) :++ bla :++ bla) :++ bla :≡ ((bla :++ bla) :++ bla) :++ bla :++ bla)

[[xs++xs++xs]++xs]++xs≡[[xs++xs]++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs ++ cs) ++ ds) ++ es ≡ ((as ++ bs) ++ cs) ++ ds ++ es
[[xs++xs++xs]++xs]++xs≡[[xs++xs]++xs]++xs++xs = list-solve
  (((bla :++ bla :++ bla) :++ bla) :++ bla :≡ ((bla :++ bla) :++ bla) :++ bla :++ bla)

[[[xs++xs]++xs]++xs]++xs≡[[xs++xs]++xs]++xs++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (((as ++ bs) ++ cs) ++ ds) ++ es ≡ ((as ++ bs) ++ cs) ++ ds ++ es
[[[xs++xs]++xs]++xs]++xs≡[[xs++xs]++xs]++xs++xs = list-solve
  ((((bla :++ bla) :++ bla) :++ bla) :++ bla :≡ ((bla :++ bla) :++ bla) :++ bla :++ bla)

xs++xs++xs++xs++xs≡[xs++xs++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ bs ++ cs ++ ds ++ es ≡ (as ++ bs ++ cs ++ ds) ++ es
xs++xs++xs++xs++xs≡[xs++xs++xs++xs]++xs = list-solve
  (bla :++ bla :++ bla :++ bla :++ bla :≡ (bla :++ bla :++ bla :++ bla) :++ bla)

xs++xs++[xs++xs]++xs≡[xs++xs++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ bs ++ (cs ++ ds) ++ es ≡ (as ++ bs ++ cs ++ ds) ++ es
xs++xs++[xs++xs]++xs≡[xs++xs++xs++xs]++xs = list-solve
  (bla :++ bla :++ (bla :++ bla) :++ bla :≡ (bla :++ bla :++ bla :++ bla) :++ bla)

xs++[xs++xs]++xs++xs≡[xs++xs++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ (bs ++ cs) ++ ds ++ es ≡ (as ++ bs ++ cs ++ ds) ++ es
xs++[xs++xs]++xs++xs≡[xs++xs++xs++xs]++xs = list-solve
  (bla :++ (bla :++ bla) :++ bla :++ bla :≡ (bla :++ bla :++ bla :++ bla) :++ bla)

xs++[xs++xs++xs]++xs≡[xs++xs++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ (bs ++ cs ++ ds) ++ es ≡ (as ++ bs ++ cs ++ ds) ++ es
xs++[xs++xs++xs]++xs≡[xs++xs++xs++xs]++xs = list-solve
  (bla :++ (bla :++ bla :++ bla) :++ bla :≡ (bla :++ bla :++ bla :++ bla) :++ bla)

xs++[[xs++xs]++xs]++xs≡[xs++xs++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ ((bs ++ cs) ++ ds) ++ es ≡ (as ++ bs ++ cs ++ ds) ++ es
xs++[[xs++xs]++xs]++xs≡[xs++xs++xs++xs]++xs = list-solve
  (bla :++ ((bla :++ bla) :++ bla) :++ bla :≡ (bla :++ bla :++ bla :++ bla) :++ bla)

[xs++xs]++xs++xs++xs≡[xs++xs++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs) ++ cs ++ ds ++ es ≡ (as ++ bs ++ cs ++ ds) ++ es
[xs++xs]++xs++xs++xs≡[xs++xs++xs++xs]++xs = list-solve
  ((bla :++ bla) :++ bla :++ bla :++ bla :≡ (bla :++ bla :++ bla :++ bla) :++ bla)

[xs++xs]++[xs++xs]++xs≡[xs++xs++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs) ++ (cs ++ ds) ++ es ≡ (as ++ bs ++ cs ++ ds) ++ es
[xs++xs]++[xs++xs]++xs≡[xs++xs++xs++xs]++xs = list-solve
  ((bla :++ bla) :++ (bla :++ bla) :++ bla :≡ (bla :++ bla :++ bla :++ bla) :++ bla)

[xs++xs++xs]++xs++xs≡[xs++xs++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs ++ cs) ++ ds ++ es ≡ (as ++ bs ++ cs ++ ds) ++ es
[xs++xs++xs]++xs++xs≡[xs++xs++xs++xs]++xs = list-solve
  ((bla :++ bla :++ bla) :++ bla :++ bla :≡ (bla :++ bla :++ bla :++ bla) :++ bla)

[[xs++xs]++xs]++xs++xs≡[xs++xs++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs) ++ cs) ++ ds ++ es ≡ (as ++ bs ++ cs ++ ds) ++ es
[[xs++xs]++xs]++xs++xs≡[xs++xs++xs++xs]++xs = list-solve
  (((bla :++ bla) :++ bla) :++ bla :++ bla :≡ (bla :++ bla :++ bla :++ bla) :++ bla)

[xs++[xs++xs]++xs]++xs≡[xs++xs++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ (bs ++ cs) ++ ds) ++ es ≡ (as ++ bs ++ cs ++ ds) ++ es
[xs++[xs++xs]++xs]++xs≡[xs++xs++xs++xs]++xs = list-solve
  ((bla :++ (bla :++ bla) :++ bla) :++ bla :≡ (bla :++ bla :++ bla :++ bla) :++ bla)

[[xs++xs]++xs++xs]++xs≡[xs++xs++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs) ++ cs ++ ds) ++ es ≡ (as ++ bs ++ cs ++ ds) ++ es
[[xs++xs]++xs++xs]++xs≡[xs++xs++xs++xs]++xs = list-solve
  (((bla :++ bla) :++ bla :++ bla) :++ bla :≡ (bla :++ bla :++ bla :++ bla) :++ bla)

[[xs++xs++xs]++xs]++xs≡[xs++xs++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs ++ cs) ++ ds) ++ es ≡ (as ++ bs ++ cs ++ ds) ++ es
[[xs++xs++xs]++xs]++xs≡[xs++xs++xs++xs]++xs = list-solve
  (((bla :++ bla :++ bla) :++ bla) :++ bla :≡ (bla :++ bla :++ bla :++ bla) :++ bla)

[[[xs++xs]++xs]++xs]++xs≡[xs++xs++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (((as ++ bs) ++ cs) ++ ds) ++ es ≡ (as ++ bs ++ cs ++ ds) ++ es
[[[xs++xs]++xs]++xs]++xs≡[xs++xs++xs++xs]++xs = list-solve
  ((((bla :++ bla) :++ bla) :++ bla) :++ bla :≡ (bla :++ bla :++ bla :++ bla) :++ bla)

xs++xs++xs++xs++xs≡[xs++[xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ bs ++ cs ++ ds ++ es ≡ (as ++ (bs ++ cs) ++ ds) ++ es
xs++xs++xs++xs++xs≡[xs++[xs++xs]++xs]++xs = list-solve
  (bla :++ bla :++ bla :++ bla :++ bla :≡ (bla :++ (bla :++ bla) :++ bla) :++ bla)

xs++xs++[xs++xs]++xs≡[xs++[xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ bs ++ (cs ++ ds) ++ es ≡ (as ++ (bs ++ cs) ++ ds) ++ es
xs++xs++[xs++xs]++xs≡[xs++[xs++xs]++xs]++xs = list-solve
  (bla :++ bla :++ (bla :++ bla) :++ bla :≡ (bla :++ (bla :++ bla) :++ bla) :++ bla)

xs++[xs++xs]++xs++xs≡[xs++[xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ (bs ++ cs) ++ ds ++ es ≡ (as ++ (bs ++ cs) ++ ds) ++ es
xs++[xs++xs]++xs++xs≡[xs++[xs++xs]++xs]++xs = list-solve
  (bla :++ (bla :++ bla) :++ bla :++ bla :≡ (bla :++ (bla :++ bla) :++ bla) :++ bla)

xs++[xs++xs++xs]++xs≡[xs++[xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ (bs ++ cs ++ ds) ++ es ≡ (as ++ (bs ++ cs) ++ ds) ++ es
xs++[xs++xs++xs]++xs≡[xs++[xs++xs]++xs]++xs = list-solve
  (bla :++ (bla :++ bla :++ bla) :++ bla :≡ (bla :++ (bla :++ bla) :++ bla) :++ bla)

xs++[[xs++xs]++xs]++xs≡[xs++[xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ ((bs ++ cs) ++ ds) ++ es ≡ (as ++ (bs ++ cs) ++ ds) ++ es
xs++[[xs++xs]++xs]++xs≡[xs++[xs++xs]++xs]++xs = list-solve
  (bla :++ ((bla :++ bla) :++ bla) :++ bla :≡ (bla :++ (bla :++ bla) :++ bla) :++ bla)

[xs++xs]++xs++xs++xs≡[xs++[xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs) ++ cs ++ ds ++ es ≡ (as ++ (bs ++ cs) ++ ds) ++ es
[xs++xs]++xs++xs++xs≡[xs++[xs++xs]++xs]++xs = list-solve
  ((bla :++ bla) :++ bla :++ bla :++ bla :≡ (bla :++ (bla :++ bla) :++ bla) :++ bla)

[xs++xs]++[xs++xs]++xs≡[xs++[xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs) ++ (cs ++ ds) ++ es ≡ (as ++ (bs ++ cs) ++ ds) ++ es
[xs++xs]++[xs++xs]++xs≡[xs++[xs++xs]++xs]++xs = list-solve
  ((bla :++ bla) :++ (bla :++ bla) :++ bla :≡ (bla :++ (bla :++ bla) :++ bla) :++ bla)

[xs++xs++xs]++xs++xs≡[xs++[xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs ++ cs) ++ ds ++ es ≡ (as ++ (bs ++ cs) ++ ds) ++ es
[xs++xs++xs]++xs++xs≡[xs++[xs++xs]++xs]++xs = list-solve
  ((bla :++ bla :++ bla) :++ bla :++ bla :≡ (bla :++ (bla :++ bla) :++ bla) :++ bla)

[[xs++xs]++xs]++xs++xs≡[xs++[xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs) ++ cs) ++ ds ++ es ≡ (as ++ (bs ++ cs) ++ ds) ++ es
[[xs++xs]++xs]++xs++xs≡[xs++[xs++xs]++xs]++xs = list-solve
  (((bla :++ bla) :++ bla) :++ bla :++ bla :≡ (bla :++ (bla :++ bla) :++ bla) :++ bla)

[xs++xs++xs++xs]++xs≡[xs++[xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs ++ cs ++ ds) ++ es ≡ (as ++ (bs ++ cs) ++ ds) ++ es
[xs++xs++xs++xs]++xs≡[xs++[xs++xs]++xs]++xs = list-solve
  ((bla :++ bla :++ bla :++ bla) :++ bla :≡ (bla :++ (bla :++ bla) :++ bla) :++ bla)

[[xs++xs]++xs++xs]++xs≡[xs++[xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs) ++ cs ++ ds) ++ es ≡ (as ++ (bs ++ cs) ++ ds) ++ es
[[xs++xs]++xs++xs]++xs≡[xs++[xs++xs]++xs]++xs = list-solve
  (((bla :++ bla) :++ bla :++ bla) :++ bla :≡ (bla :++ (bla :++ bla) :++ bla) :++ bla)

[[xs++xs++xs]++xs]++xs≡[xs++[xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs ++ cs) ++ ds) ++ es ≡ (as ++ (bs ++ cs) ++ ds) ++ es
[[xs++xs++xs]++xs]++xs≡[xs++[xs++xs]++xs]++xs = list-solve
  (((bla :++ bla :++ bla) :++ bla) :++ bla :≡ (bla :++ (bla :++ bla) :++ bla) :++ bla)

[[[xs++xs]++xs]++xs]++xs≡[xs++[xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (((as ++ bs) ++ cs) ++ ds) ++ es ≡ (as ++ (bs ++ cs) ++ ds) ++ es
[[[xs++xs]++xs]++xs]++xs≡[xs++[xs++xs]++xs]++xs = list-solve
  ((((bla :++ bla) :++ bla) :++ bla) :++ bla :≡ (bla :++ (bla :++ bla) :++ bla) :++ bla)

xs++xs++xs++xs++xs≡[[xs++xs]++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ bs ++ cs ++ ds ++ es ≡ ((as ++ bs) ++ cs ++ ds) ++ es
xs++xs++xs++xs++xs≡[[xs++xs]++xs++xs]++xs = list-solve
  (bla :++ bla :++ bla :++ bla :++ bla :≡ ((bla :++ bla) :++ bla :++ bla) :++ bla)

xs++xs++[xs++xs]++xs≡[[xs++xs]++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ bs ++ (cs ++ ds) ++ es ≡ ((as ++ bs) ++ cs ++ ds) ++ es
xs++xs++[xs++xs]++xs≡[[xs++xs]++xs++xs]++xs = list-solve
  (bla :++ bla :++ (bla :++ bla) :++ bla :≡ ((bla :++ bla) :++ bla :++ bla) :++ bla)

xs++[xs++xs]++xs++xs≡[[xs++xs]++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ (bs ++ cs) ++ ds ++ es ≡ ((as ++ bs) ++ cs ++ ds) ++ es
xs++[xs++xs]++xs++xs≡[[xs++xs]++xs++xs]++xs = list-solve
  (bla :++ (bla :++ bla) :++ bla :++ bla :≡ ((bla :++ bla) :++ bla :++ bla) :++ bla)

xs++[xs++xs++xs]++xs≡[[xs++xs]++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ (bs ++ cs ++ ds) ++ es ≡ ((as ++ bs) ++ cs ++ ds) ++ es
xs++[xs++xs++xs]++xs≡[[xs++xs]++xs++xs]++xs = list-solve
  (bla :++ (bla :++ bla :++ bla) :++ bla :≡ ((bla :++ bla) :++ bla :++ bla) :++ bla)

xs++[[xs++xs]++xs]++xs≡[[xs++xs]++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ ((bs ++ cs) ++ ds) ++ es ≡ ((as ++ bs) ++ cs ++ ds) ++ es
xs++[[xs++xs]++xs]++xs≡[[xs++xs]++xs++xs]++xs = list-solve
  (bla :++ ((bla :++ bla) :++ bla) :++ bla :≡ ((bla :++ bla) :++ bla :++ bla) :++ bla)

[xs++xs]++xs++xs++xs≡[[xs++xs]++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs) ++ cs ++ ds ++ es ≡ ((as ++ bs) ++ cs ++ ds) ++ es
[xs++xs]++xs++xs++xs≡[[xs++xs]++xs++xs]++xs = list-solve
  ((bla :++ bla) :++ bla :++ bla :++ bla :≡ ((bla :++ bla) :++ bla :++ bla) :++ bla)

[xs++xs]++[xs++xs]++xs≡[[xs++xs]++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs) ++ (cs ++ ds) ++ es ≡ ((as ++ bs) ++ cs ++ ds) ++ es
[xs++xs]++[xs++xs]++xs≡[[xs++xs]++xs++xs]++xs = list-solve
  ((bla :++ bla) :++ (bla :++ bla) :++ bla :≡ ((bla :++ bla) :++ bla :++ bla) :++ bla)

[xs++xs++xs]++xs++xs≡[[xs++xs]++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs ++ cs) ++ ds ++ es ≡ ((as ++ bs) ++ cs ++ ds) ++ es
[xs++xs++xs]++xs++xs≡[[xs++xs]++xs++xs]++xs = list-solve
  ((bla :++ bla :++ bla) :++ bla :++ bla :≡ ((bla :++ bla) :++ bla :++ bla) :++ bla)

[[xs++xs]++xs]++xs++xs≡[[xs++xs]++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs) ++ cs) ++ ds ++ es ≡ ((as ++ bs) ++ cs ++ ds) ++ es
[[xs++xs]++xs]++xs++xs≡[[xs++xs]++xs++xs]++xs = list-solve
  (((bla :++ bla) :++ bla) :++ bla :++ bla :≡ ((bla :++ bla) :++ bla :++ bla) :++ bla)

[xs++xs++xs++xs]++xs≡[[xs++xs]++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs ++ cs ++ ds) ++ es ≡ ((as ++ bs) ++ cs ++ ds) ++ es
[xs++xs++xs++xs]++xs≡[[xs++xs]++xs++xs]++xs = list-solve
  ((bla :++ bla :++ bla :++ bla) :++ bla :≡ ((bla :++ bla) :++ bla :++ bla) :++ bla)

[xs++[xs++xs]++xs]++xs≡[[xs++xs]++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ (bs ++ cs) ++ ds) ++ es ≡ ((as ++ bs) ++ cs ++ ds) ++ es
[xs++[xs++xs]++xs]++xs≡[[xs++xs]++xs++xs]++xs = list-solve
  ((bla :++ (bla :++ bla) :++ bla) :++ bla :≡ ((bla :++ bla) :++ bla :++ bla) :++ bla)

[[xs++xs++xs]++xs]++xs≡[[xs++xs]++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs ++ cs) ++ ds) ++ es ≡ ((as ++ bs) ++ cs ++ ds) ++ es
[[xs++xs++xs]++xs]++xs≡[[xs++xs]++xs++xs]++xs = list-solve
  (((bla :++ bla :++ bla) :++ bla) :++ bla :≡ ((bla :++ bla) :++ bla :++ bla) :++ bla)

[[[xs++xs]++xs]++xs]++xs≡[[xs++xs]++xs++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (((as ++ bs) ++ cs) ++ ds) ++ es ≡ ((as ++ bs) ++ cs ++ ds) ++ es
[[[xs++xs]++xs]++xs]++xs≡[[xs++xs]++xs++xs]++xs = list-solve
  ((((bla :++ bla) :++ bla) :++ bla) :++ bla :≡ ((bla :++ bla) :++ bla :++ bla) :++ bla)

xs++xs++xs++xs++xs≡[[xs++xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ bs ++ cs ++ ds ++ es ≡ ((as ++ bs ++ cs) ++ ds) ++ es
xs++xs++xs++xs++xs≡[[xs++xs++xs]++xs]++xs = list-solve
  (bla :++ bla :++ bla :++ bla :++ bla :≡ ((bla :++ bla :++ bla) :++ bla) :++ bla)

xs++xs++[xs++xs]++xs≡[[xs++xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ bs ++ (cs ++ ds) ++ es ≡ ((as ++ bs ++ cs) ++ ds) ++ es
xs++xs++[xs++xs]++xs≡[[xs++xs++xs]++xs]++xs = list-solve
  (bla :++ bla :++ (bla :++ bla) :++ bla :≡ ((bla :++ bla :++ bla) :++ bla) :++ bla)

xs++[xs++xs]++xs++xs≡[[xs++xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ (bs ++ cs) ++ ds ++ es ≡ ((as ++ bs ++ cs) ++ ds) ++ es
xs++[xs++xs]++xs++xs≡[[xs++xs++xs]++xs]++xs = list-solve
  (bla :++ (bla :++ bla) :++ bla :++ bla :≡ ((bla :++ bla :++ bla) :++ bla) :++ bla)

xs++[xs++xs++xs]++xs≡[[xs++xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ (bs ++ cs ++ ds) ++ es ≡ ((as ++ bs ++ cs) ++ ds) ++ es
xs++[xs++xs++xs]++xs≡[[xs++xs++xs]++xs]++xs = list-solve
  (bla :++ (bla :++ bla :++ bla) :++ bla :≡ ((bla :++ bla :++ bla) :++ bla) :++ bla)

xs++[[xs++xs]++xs]++xs≡[[xs++xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ ((bs ++ cs) ++ ds) ++ es ≡ ((as ++ bs ++ cs) ++ ds) ++ es
xs++[[xs++xs]++xs]++xs≡[[xs++xs++xs]++xs]++xs = list-solve
  (bla :++ ((bla :++ bla) :++ bla) :++ bla :≡ ((bla :++ bla :++ bla) :++ bla) :++ bla)

[xs++xs]++xs++xs++xs≡[[xs++xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs) ++ cs ++ ds ++ es ≡ ((as ++ bs ++ cs) ++ ds) ++ es
[xs++xs]++xs++xs++xs≡[[xs++xs++xs]++xs]++xs = list-solve
  ((bla :++ bla) :++ bla :++ bla :++ bla :≡ ((bla :++ bla :++ bla) :++ bla) :++ bla)

[xs++xs]++[xs++xs]++xs≡[[xs++xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs) ++ (cs ++ ds) ++ es ≡ ((as ++ bs ++ cs) ++ ds) ++ es
[xs++xs]++[xs++xs]++xs≡[[xs++xs++xs]++xs]++xs = list-solve
  ((bla :++ bla) :++ (bla :++ bla) :++ bla :≡ ((bla :++ bla :++ bla) :++ bla) :++ bla)

[xs++xs++xs]++xs++xs≡[[xs++xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs ++ cs) ++ ds ++ es ≡ ((as ++ bs ++ cs) ++ ds) ++ es
[xs++xs++xs]++xs++xs≡[[xs++xs++xs]++xs]++xs = list-solve
  ((bla :++ bla :++ bla) :++ bla :++ bla :≡ ((bla :++ bla :++ bla) :++ bla) :++ bla)

[[xs++xs]++xs]++xs++xs≡[[xs++xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs) ++ cs) ++ ds ++ es ≡ ((as ++ bs ++ cs) ++ ds) ++ es
[[xs++xs]++xs]++xs++xs≡[[xs++xs++xs]++xs]++xs = list-solve
  (((bla :++ bla) :++ bla) :++ bla :++ bla :≡ ((bla :++ bla :++ bla) :++ bla) :++ bla)

[xs++xs++xs++xs]++xs≡[[xs++xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs ++ cs ++ ds) ++ es ≡ ((as ++ bs ++ cs) ++ ds) ++ es
[xs++xs++xs++xs]++xs≡[[xs++xs++xs]++xs]++xs = list-solve
  ((bla :++ bla :++ bla :++ bla) :++ bla :≡ ((bla :++ bla :++ bla) :++ bla) :++ bla)

[xs++[xs++xs]++xs]++xs≡[[xs++xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ (bs ++ cs) ++ ds) ++ es ≡ ((as ++ bs ++ cs) ++ ds) ++ es
[xs++[xs++xs]++xs]++xs≡[[xs++xs++xs]++xs]++xs = list-solve
  ((bla :++ (bla :++ bla) :++ bla) :++ bla :≡ ((bla :++ bla :++ bla) :++ bla) :++ bla)

[[xs++xs]++xs++xs]++xs≡[[xs++xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs) ++ cs ++ ds) ++ es ≡ ((as ++ bs ++ cs) ++ ds) ++ es
[[xs++xs]++xs++xs]++xs≡[[xs++xs++xs]++xs]++xs = list-solve
  (((bla :++ bla) :++ bla :++ bla) :++ bla :≡ ((bla :++ bla :++ bla) :++ bla) :++ bla)

[[[xs++xs]++xs]++xs]++xs≡[[xs++xs++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (((as ++ bs) ++ cs) ++ ds) ++ es ≡ ((as ++ bs ++ cs) ++ ds) ++ es
[[[xs++xs]++xs]++xs]++xs≡[[xs++xs++xs]++xs]++xs = list-solve
  ((((bla :++ bla) :++ bla) :++ bla) :++ bla :≡ ((bla :++ bla :++ bla) :++ bla) :++ bla)

xs++xs++xs++xs++xs≡[[[xs++xs]++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ bs ++ cs ++ ds ++ es ≡ (((as ++ bs) ++ cs) ++ ds) ++ es
xs++xs++xs++xs++xs≡[[[xs++xs]++xs]++xs]++xs = list-solve
  (bla :++ bla :++ bla :++ bla :++ bla :≡ (((bla :++ bla) :++ bla) :++ bla) :++ bla)

xs++xs++[xs++xs]++xs≡[[[xs++xs]++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ bs ++ (cs ++ ds) ++ es ≡ (((as ++ bs) ++ cs) ++ ds) ++ es
xs++xs++[xs++xs]++xs≡[[[xs++xs]++xs]++xs]++xs = list-solve
  (bla :++ bla :++ (bla :++ bla) :++ bla :≡ (((bla :++ bla) :++ bla) :++ bla) :++ bla)

xs++[xs++xs]++xs++xs≡[[[xs++xs]++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ (bs ++ cs) ++ ds ++ es ≡ (((as ++ bs) ++ cs) ++ ds) ++ es
xs++[xs++xs]++xs++xs≡[[[xs++xs]++xs]++xs]++xs = list-solve
  (bla :++ (bla :++ bla) :++ bla :++ bla :≡ (((bla :++ bla) :++ bla) :++ bla) :++ bla)

xs++[xs++xs++xs]++xs≡[[[xs++xs]++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ (bs ++ cs ++ ds) ++ es ≡ (((as ++ bs) ++ cs) ++ ds) ++ es
xs++[xs++xs++xs]++xs≡[[[xs++xs]++xs]++xs]++xs = list-solve
  (bla :++ (bla :++ bla :++ bla) :++ bla :≡ (((bla :++ bla) :++ bla) :++ bla) :++ bla)

xs++[[xs++xs]++xs]++xs≡[[[xs++xs]++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → as ++ ((bs ++ cs) ++ ds) ++ es ≡ (((as ++ bs) ++ cs) ++ ds) ++ es
xs++[[xs++xs]++xs]++xs≡[[[xs++xs]++xs]++xs]++xs = list-solve
  (bla :++ ((bla :++ bla) :++ bla) :++ bla :≡ (((bla :++ bla) :++ bla) :++ bla) :++ bla)

[xs++xs]++xs++xs++xs≡[[[xs++xs]++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs) ++ cs ++ ds ++ es ≡ (((as ++ bs) ++ cs) ++ ds) ++ es
[xs++xs]++xs++xs++xs≡[[[xs++xs]++xs]++xs]++xs = list-solve
  ((bla :++ bla) :++ bla :++ bla :++ bla :≡ (((bla :++ bla) :++ bla) :++ bla) :++ bla)

[xs++xs]++[xs++xs]++xs≡[[[xs++xs]++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs) ++ (cs ++ ds) ++ es ≡ (((as ++ bs) ++ cs) ++ ds) ++ es
[xs++xs]++[xs++xs]++xs≡[[[xs++xs]++xs]++xs]++xs = list-solve
  ((bla :++ bla) :++ (bla :++ bla) :++ bla :≡ (((bla :++ bla) :++ bla) :++ bla) :++ bla)

[xs++xs++xs]++xs++xs≡[[[xs++xs]++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs ++ cs) ++ ds ++ es ≡ (((as ++ bs) ++ cs) ++ ds) ++ es
[xs++xs++xs]++xs++xs≡[[[xs++xs]++xs]++xs]++xs = list-solve
  ((bla :++ bla :++ bla) :++ bla :++ bla :≡ (((bla :++ bla) :++ bla) :++ bla) :++ bla)

[[xs++xs]++xs]++xs++xs≡[[[xs++xs]++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs) ++ cs) ++ ds ++ es ≡ (((as ++ bs) ++ cs) ++ ds) ++ es
[[xs++xs]++xs]++xs++xs≡[[[xs++xs]++xs]++xs]++xs = list-solve
  (((bla :++ bla) :++ bla) :++ bla :++ bla :≡ (((bla :++ bla) :++ bla) :++ bla) :++ bla)

[xs++xs++xs++xs]++xs≡[[[xs++xs]++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ bs ++ cs ++ ds) ++ es ≡ (((as ++ bs) ++ cs) ++ ds) ++ es
[xs++xs++xs++xs]++xs≡[[[xs++xs]++xs]++xs]++xs = list-solve
  ((bla :++ bla :++ bla :++ bla) :++ bla :≡ (((bla :++ bla) :++ bla) :++ bla) :++ bla)

[xs++[xs++xs]++xs]++xs≡[[[xs++xs]++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → (as ++ (bs ++ cs) ++ ds) ++ es ≡ (((as ++ bs) ++ cs) ++ ds) ++ es
[xs++[xs++xs]++xs]++xs≡[[[xs++xs]++xs]++xs]++xs = list-solve
  ((bla :++ (bla :++ bla) :++ bla) :++ bla :≡ (((bla :++ bla) :++ bla) :++ bla) :++ bla)

[[xs++xs]++xs++xs]++xs≡[[[xs++xs]++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs) ++ cs ++ ds) ++ es ≡ (((as ++ bs) ++ cs) ++ ds) ++ es
[[xs++xs]++xs++xs]++xs≡[[[xs++xs]++xs]++xs]++xs = list-solve
  (((bla :++ bla) :++ bla :++ bla) :++ bla :≡ (((bla :++ bla) :++ bla) :++ bla) :++ bla)

[[xs++xs++xs]++xs]++xs≡[[[xs++xs]++xs]++xs]++xs : ∀ {a} {A : Set a}
  → (as bs cs ds es : List A)
  → ((as ++ bs ++ cs) ++ ds) ++ es ≡ (((as ++ bs) ++ cs) ++ ds) ++ es
[[xs++xs++xs]++xs]++xs≡[[[xs++xs]++xs]++xs]++xs = list-solve
  (((bla :++ bla :++ bla) :++ bla) :++ bla :≡ (((bla :++ bla) :++ bla) :++ bla) :++ bla)
