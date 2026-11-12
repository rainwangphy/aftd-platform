import AFTD.Prelude

/-!
# bit_persuasion_even_coord

Topic: mechanism_design   Node: 3c7bef686452

Provenance: formalization of a published result. Source: arXiv:2606.22226

The type of coordinates of the two-layer prior for 2m states, defined as the coproduct type of ({A : Finset (Fin (2 * m)) // A.card = m - 1} × Fin (m + 1)) and ({B : Finset (Fin (2 * m)) // B.card = m} × Fin (3 * m)), pairing each (m-1)-subset of Fin (2 * m) with a multiplicity index in Fin (m + 1) and each m-subset of Fin (2 * m) with a multiplicity index in Fin (3 * m).
-/

open Finset in
/-- The coordinate type of the two-layer prior on 2m states: (m-1)-subsets with multiplicity m+1, and m-subsets with multiplicity 3m. -/
abbrev bit_persuasion_even_coord (m : ℕ) :=
  ({A : Finset (Fin (2 * m)) // A.card = m - 1} × Fin (m + 1)) ⊕
  ({B : Finset (Fin (2 * m)) // B.card = m} × Fin (3 * m))
