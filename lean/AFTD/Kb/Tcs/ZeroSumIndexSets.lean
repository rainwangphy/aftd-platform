import AFTD.Prelude

/-!
# zero_sum_index_sets

Topic: combinatorics   Node: 6e4a7e114757

Provenance: formalization of a published result. Source: arXiv:2611.20197

Given an additive commutative group G, a natural number N, and a sequence U : Fin N → G, zero_sum_index_sets U is the finset (of type Finset (Finset (Fin N))) of all nonempty subsets E of Fin N such that the sum of U j over j ∈ E equals 0.
-/

open Classical in
/-- The finset of nonempty zero-sum index sets of a sequence U of N elements in an abelian group G. -/
noncomputable def zero_sum_index_sets {G : Type*} [AddCommGroup G] {N : ℕ} (U : Fin N → G) :
    Finset (Finset (Fin N)) :=
  Finset.univ.filter fun E => E.Nonempty ∧ ∑ j ∈ E, U j = 0
