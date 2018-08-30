module NCILL.Ctx where

open import Data.List

open import NCILL.Types

-- CONTEXT
------------------------------------------------------------------------

-- Context is a _list_ without. Not a set or multiset.
-- That makes proving very direct.
Ctx = List Ty
