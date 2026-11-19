import AFTD.Prelude
import AFTD.Kb.Tcs.LinIneq

/-!
# lin_ineq_unary_size

Topic: proof_complexity   Node: 235766ba468b

Provenance: formalization of a published result. Source: arXiv:2611.24548 Section 2.1, Definition 4.1

The unary size of a linear inequality c^T x ≥ d, defined as the sum of absolute values of its coefficients plus |d| + 1.
-/

/-- Unary size of a linear inequality c^T x ≥ d: sum of |c_i| plus |d| + 1. -/
def lin_ineq_unary_size {n : ℕ} (L : LinIneq n) : ℕ :=
  (∑ i : Fin n, (L.coeffs i).natAbs) + L.const.natAbs + 1
