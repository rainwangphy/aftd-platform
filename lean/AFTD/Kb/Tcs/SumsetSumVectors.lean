import AFTD.Prelude

/-!
# sumset_sum_vectors

Topic: combinatorics   Node: c0fec3721d2b

Provenance: formalization of a published result. Source: arXiv:2611.07303, Definition 2.2 and Eq (1.3)

The set X_{h,k} is defined as the set of all vectors x : Fin k → ℤ satisfying (∀ i, 0 ≤ x i) and ∑ i, x i = (h : ℤ).
-/

/-- The set X_{h,k} of nonnegative integer vectors summing to h. -/
def sumset_sum_vectors (h k : ℕ) : Set (Fin k → ℤ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = (h : ℤ)}
