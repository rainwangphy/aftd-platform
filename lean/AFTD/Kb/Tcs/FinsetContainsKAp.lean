import AFTD.Prelude

/-!
# finset_contains_k_ap

Topic: combinatorics   Node: eba11e74c30c

Provenance: formalization of a published result. Source: arXiv:2610.26243, Section 1

A subset s of Fin n contains a k-term arithmetic progression if there exist a and d with 1 ≤ d such that a + i * d is in s for all 0 ≤ i < k.
-/

/-- Predicate that a subset of Fin n contains a k-term arithmetic progression. -/
def finset_contains_k_ap (n k : ℕ) (s : Finset (Fin n)) : Prop := ∃ (a d : ℕ), 1 ≤ d ∧ ∀ i < k, ∃ x ∈ s, (x : ℕ) = a + i * d
