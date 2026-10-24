import AFTD.Prelude

/-!
# distinct_subset_sums_admissible

Topic: combinatorics   Node: 146b7b45298f

Provenance: formalization of a published result. Source: arXiv:2610.26970 Def 1.1

A sequence of vectors a : Fin n → Fin k → ℕ is admissible if any two subsets S, T ⊆ Fin n with the same subset sum ∑_{i ∈ S} a_i = ∑_{i ∈ T} a_i are equal.
-/

/-- A sequence of vectors in N^k is admissible if all of its subset sums are distinct. -/
def distinct_subset_sums_admissible {n k : ℕ} (a : Fin n → Fin k → ℕ) : Prop :=
  ∀ (S T : Finset (Fin n)), (∑ i ∈ S, a i) = (∑ i ∈ T, a i) → S = T
