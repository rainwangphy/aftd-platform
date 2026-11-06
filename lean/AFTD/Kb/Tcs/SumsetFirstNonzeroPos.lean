import AFTD.Prelude

/-!
# sumset_first_nonzero_pos

Topic: combinatorics   Node: 95e7feaf76e3

Provenance: formalization of a published result. Source: arXiv:2611.07303, Definition 3.1

An integer vector has its first nonzero entry positive if there is an index i such that all previous entries are zero and the i-th entry is strictly positive.
-/

/-- Predicate that the first nonzero coordinate of an integer vector is positive. -/
def sumset_first_nonzero_pos {k : ℕ} (d : Fin k → ℤ) : Prop :=
  ∃ i : Fin k, (∀ j < i, d j = 0) ∧ 0 < d i
