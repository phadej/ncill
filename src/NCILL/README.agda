-- Non-Commutative Linear Lambda Calculus
--
-- Relations and non-commutative linear logic
-- by Carolyn Brown, Doug Gurr
-- https://www.sciencedirect.com/science/article/pii/0022404994001472
--
-- Frank Pfenning's lectures on logic influeced the proof making.
-- The proof is essentially the same as his proof for STLC,
-- yet in Agda (not informal / Twelf) and for NCILL.
-- Cut-Elimination proof for NCILL is easy to mechanize, as
-- contexts are lists, not sets (STLC) or multisets (ILL).
--
-- Rendered HTML docs are at http://oleg.fi/ncill/
-- Source code is at https://github.com/phadej/ncill
--
module NCILL.README where

-- Non-commutative Intuitinistic Linear Logic
------------------------------------------------------------------------
--
-- ∙ Types

import NCILL.Types

-- ∙ Context is just a set of types: Ctx = List Ty

import NCILL.Ctx

-- ∙ Sqnt are sequents

import NCILL.Sequent

-- ∙ Sqnt⁺ are sequents with Cut

import NCILL.SequentPlus

-- ∙ We prove Cut Elimination Theorem (Soundness), Completeness is trivial

import NCILL.Cut

-- ⋯ using Admissibility of Cut lemma

import NCILL.Admit

-- ∙ For development, you can

import NCILL

-- Examples
------------------------------------------------------------------------

-- ∙ We show terms for many equivalences in NCILL:
--   ∘ Quantale structure: Monoids of ⊗ and ♯1; ⊕ and ♯0; & and ♯⊤,
--     distributivity
--   ∘ More equivalences from Girard's Linear Logic (only ⊗-comm doesn't hold!)
--   ∘ Example of difference between ⊸ and ⊸ʳ
--
import NCILL.Examples.Equivalences

-- ∙ Though CUT is admissible in NCILL, η-reductions aren't performed.
--   This example shows ⊗ η and β -reductions.
--   ∘ original and η-reduced term aren't the same, yet logically they are 
--   ∘ β involves CUT, and terms are definitionally equal
--   ∘ we compare that to Agda's own behaviour
--
import NCILL.Examples.EtaBeta

-- Extras
------------------------------------------------------------------------

-- ∙ there are some extras to write the proofs

import ListExtras          -- few additional list related lemmas
import Simple-list-solver  -- solver for list concatenations (simpler to use than monoid-solver)
import AssocProofs         -- associativity lemmas up to 5 arguments "pre-proved"
