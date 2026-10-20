import AFTD.Prelude

/-!
# saddle_gap_first_payoff_pure_ge_of_sub_ge

Topic: equilibria   Node: 224cc1f89bb6

Provenance: helper lemma. arXiv:2610.25524 Lemma 4.2

For an n-by-n matrix A with nonnegative entries, probability vectors a and b in `stdSimplex ℝ (Fin n)`, and real number v, if `Matrix.vecMul a.val A k - Matrix.mulVec A b.val k ≥ v` for all k in Fin n, then `Matrix.vecMul a.val A k ≥ v` for all k in Fin n.
-/

/-- Pure column payoff is at least v when the difference between first and second marginal payoffs is at least v and the matrix is nonnegative. -/
lemma saddle_gap_first_payoff_pure_ge_of_sub_ge {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA_nonneg : ∀ i j, 0 ≤ A i j) (a b : stdSimplex ℝ (Fin n)) (v : ℝ) (h : ∀ k : Fin n, Matrix.vecMul a.val A k - Matrix.mulVec A b.val k ≥ v) (k : Fin n) : Matrix.vecMul a.val A k ≥ v := by
  have h_nonneg : 0 ≤ Matrix.mulVec A b.val k := by
    simp [Matrix.mulVec, dotProduct]
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (hA_nonneg k i) (b.2.1 i)
  have hk := h k
  linarith
