import AFTD.Prelude

/-!
# energy_filter_crossover_quad_form_nonneg

Topic: statistical_mechanics   Node: a0d0c3d8393c

Provenance: helper lemma. arXiv:2405.02158

For any vector v in R^3, the quadratic form v^T L^{-1} v is nonnegative, where L is the 3x3 real matrix with diagonal 2 and adjacent off-diagonal entries -1.
-/

/-- OP-802 partial: The quadratic form defined by the inverse crossover coupling matrix L is positive semidefinite. -/
theorem energy_filter_crossover_quad_form_nonneg (v : Fin 3 → ℝ) :
    let L : Matrix (Fin 3) (Fin 3) ℝ := !![2, -1, 0; -1, 2, -1; 0, -1, 2]
    0 ≤ dotProduct v (Matrix.mulVec L⁻¹ v) := by
  intro L
  let M : Matrix (Fin 3) (Fin 3) ℝ := !![3/4, 1/2, 1/4; 1/2, 1, 1/2; 1/4, 1/2, 3/4]
  have hLM : L * M = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> {
      simp [L, M, Matrix.mul_apply, Fin.sum_univ_three]
      try ring
    }
  have hinv : L⁻¹ = M := Matrix.inv_eq_right_inv hLM
  rw [hinv]
  have h_eq : dotProduct v (Matrix.mulVec M v) =
      (3/4) * (v 0 + 2/3 * v 1 + 1/3 * v 2)^2 +
      (2/3) * (v 1 + 1/2 * v 2)^2 +
      (1/2) * (v 2)^2 := by
    simp [dotProduct, Matrix.mulVec, M, Fin.sum_univ_three]
    ring
  rw [h_eq]
  positivity
