import AFTD.Prelude

/-!
# charity

Topic: fair_division   Node: 912b11be3d89

Provenance: formalization of a published result. Source: arXiv:2611.12740 Section 2

Given natural numbers m and n and an allocation X : Fin n → Finset (Fin m), charity X is the finset of items in Fin m not allocated to any agent, defined as Finset.univ \ Finset.univ.biUnion X.
-/

/-- The charity set of an allocation is the finset of unallocated items in Fin m. -/
def charity {m n : ℕ} (X : Fin n → Finset (Fin m)) : Finset (Fin m) := Finset.univ \ Finset.univ.biUnion X
