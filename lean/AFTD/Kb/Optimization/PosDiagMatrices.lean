import AFTD.Prelude

/-!
# pos_diag_matrices

Topic: lp_duality   Node: b2dfe45bc263

Provenance: formalization of a published result. Source: arXiv:2611.07815 Section 1.1

The set of positive diagonal matrices in ℝ^(n × n), defined as diagonal matrices whose diagonal entries are all strictly positive.
-/

/-- The set of positive diagonal n-by-n real matrices, with strictly positive diagonal entries. -/
def pos_diag_matrices (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) := { Matrix.diagonal d | (d : Fin n → ℝ) (_ : ∀ i, 0 < d i) }
