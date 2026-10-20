import AFTD.Prelude

/-!
# dotProduct_mulVec_ge_inf'

Topic: equilibria   Node: 807031f2b34e

Provenance: helper lemma. arXiv:2610.25524 Lemma 4.1

For any strategy x in the standard simplex stdSimplex ℝ (Fin n) and any matrix A, the self-payoff xᵀ A x is at least the minimum over j of (x ᵥ* A) j.
-/

/-- Self-payoff xᵀ A x is at least the minimum pure column payoff min_j xᵀ A e_j. -/
lemma dotProduct_mulVec_ge_inf' {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℝ) (x : stdSimplex ℝ (Fin n)) :
    Finset.univ.inf' Finset.univ_nonempty (fun j => Matrix.vecMul x.val A j) ≤
      dotProduct x.val (Matrix.mulVec A x.val) := by
  have hdot : dotProduct x.val (Matrix.mulVec A x.val)
      = ∑ j, x.val j * (Matrix.vecMul x.val A j) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.vecMul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hdot]
  have hbound : ∀ j ∈ Finset.univ,
      x.val j * (Finset.univ.inf' Finset.univ_nonempty (fun j => Matrix.vecMul x.val A j))
        ≤ x.val j * (Matrix.vecMul x.val A j) := by
    intro j _
    exact mul_le_mul_of_nonneg_left
      (Finset.inf'_le (fun j => Matrix.vecMul x.val A j) (Finset.mem_univ j))
      (x.property.1 j)
  have hsum := Finset.sum_le_sum hbound
  rwa [← Finset.sum_mul, x.property.2, one_mul] at hsum
