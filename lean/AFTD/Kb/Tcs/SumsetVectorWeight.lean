import AFTD.Prelude

/-!
# sumset_vector_weight

Topic: combinatorics   Node: e4af75deb954

Provenance: formalization of a published result. Source: arXiv:2611.07303, Definition 3.1

The weight of an integer vector d is the sum of its positive parts max(d_i, 0).
-/

/-- The weight w(d) of an integer vector d, defined as the sum of max(d_i, 0). -/
def sumset_vector_weight {k : ℕ} (d : Fin k → ℤ) : ℤ :=
  ∑ i : Fin k, max (d i) 0
