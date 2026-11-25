import AFTD.Prelude

/-!
# sufficient_matrix_rearrangement_iff

Topic: lp_duality   Node: d6700192092d

Provenance: formalization of a published result. Source: arXiv:2611.07815 Proposition 9.1

Let κ ≥ 0 and P, N ≥ 0 be scalars. Then (1 + 4 * κ) * P - N ≥ 0 if and only if P - N ≥ - (2 * κ / (1 + 2 * κ)) * (P + N).
-/

/-- Algebraic rearrangement for the P*(kappa) condition (arXiv:2611.07815 Proposition 9.1). -/
lemma sufficient_matrix_rearrangement_iff (κ P N : ℝ) (hκ : 0 ≤ κ) (hP : 0 ≤ P) (hN : 0 ≤ N) :
    0 ≤ (1 + 4 * κ) * P - N ↔ - (2 * κ / (1 + 2 * κ)) * (P + N) ≤ P - N := by
  have hden : (0:ℝ) < 1 + 2 * κ := by linarith
  rw [neg_mul, div_mul_eq_mul_div, ← neg_div, div_le_iff₀ hden]
  constructor <;> intro h <;> nlinarith
