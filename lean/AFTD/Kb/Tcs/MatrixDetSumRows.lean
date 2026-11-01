import AFTD.Prelude

/-!
# matrix_det_sum_rows

Topic: graphs   Node: 8f88e4ee9775

Provenance: helper lemma. step towards tournament_arborescence_hadamard_bound

Multilinearity of the determinant in the rows: the determinant of a sum of matrices ∑_{k<m} A_k is the sum, over all functions f : Fin n → Fin m choosing one summand per row, of the determinant of the matrix whose i-th row is the i-th row of A_{f i}.
-/

/-- Row-wise multilinearity: `det` of a sum of matrices expands as a sum over the choice of one summand per row. -/
theorem matrix_det_sum_rows {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) : (∑ k : Fin m, A k).det = ∑ f : Fin n → Fin m, (Matrix.of (fun i j => A (f i) i j)).det := by
  -- Use the determinant formula expanding along rows (the transpose of `det_apply'`).
  have hdet : ∀ M : Matrix (Fin n) (Fin n) ℝ,
      M.det = ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℝ) * ∏ i, M i (σ i) := by
    intro M
    rw [← Matrix.det_transpose M, Matrix.det_apply']
    rfl
  rw [hdet (∑ k : Fin m, A k)]
  simp only [Matrix.sum_apply]
  rw [show (∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℝ) * ∏ i, ∑ k : Fin m, A k i (σ i))
      = ∑ σ : Equiv.Perm (Fin n), ∑ f : Fin n → Fin m, (Equiv.Perm.sign σ : ℝ) * ∏ i, A (f i) i (σ i) from ?_]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro f _
    rw [hdet (Matrix.of (fun i j => A (f i) i j))]
    simp
  · apply Finset.sum_congr rfl
    intro σ _
    rw [Finset.prod_univ_sum]
    rw [Fintype.piFinset_univ]
    rw [Finset.mul_sum]
