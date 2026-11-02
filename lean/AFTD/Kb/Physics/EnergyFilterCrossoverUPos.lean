import AFTD.Prelude

/-!
# energy_filter_crossover_u_pos

Topic: statistical_mechanics   Node: dc7c2af7c694

Provenance: helper lemma. arXiv:2405.02158

For any tau > 0, real c, natural number p, and positive integer q, let D = p^2 + q^2; then the quadratic Gaussian coefficient u = pi^2 * q^2 / (2 * tau^2) + pi^2 * c^2 * q^4 / (4 * D) is strictly positive.
-/

/-- OP-802 partial: The quadratic Gaussian decay rate u in the crossover sum S_2 is strictly positive for any filter width and coupling. -/
theorem energy_filter_crossover_u_pos (τ c : ℝ) (hτ : 0 < τ) (p q : ℕ) (hq : 0 < q) :
    let D : ℝ := (p : ℝ)^2 + (q : ℝ)^2
    0 < Real.pi^2 * (q : ℝ)^2 / (2 * τ^2) + Real.pi^2 * c^2 * (q : ℝ)^4 / (4 * D) := by
  intro D
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hpi : 0 < Real.pi := Real.pi_pos
  have hterm : 0 < Real.pi^2 * (q:ℝ)^2 / (2 * τ^2) := by positivity
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hterm2 : 0 ≤ Real.pi^2 * c^2 * (q:ℝ)^4 / (4 * D) := by positivity
  linarith
