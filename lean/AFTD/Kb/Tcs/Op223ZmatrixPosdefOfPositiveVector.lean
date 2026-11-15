import AFTD.Prelude

/-!
# op223_zmatrix_posdef_of_positive_vector

Topic: graphs   Node: ef9d86cba1cd

Provenance: helper lemma. Standard strict diagonal dominance after a positive diagonal scaling.

A real symmetric matrix with nonpositive off-diagonal entries is positive definite if it maps some strictly positive vector to a strictly positive vector.
-/

private lemma op223_zmatrix_posdef_of_positive_vector_sum_ineq {ι : Type*} [Fintype ι]
    (A : ι → ι → ℝ) (hsym : ∀ i j, A j i = A i j)
    (hA : ∀ i j, i ≠ j → A i j ≤ 0) (w : ι → ℝ) :
    ∑ i, (∑ j, A i j) * (w i)^2 ≤ ∑ i, ∑ j, A i j * w i * w j := by
  have hpair : ∀ i j, A i j * (w i)^2 + A i j * (w j)^2 ≤ 2 * (A i j * w i * w j) := by
    intro i j
    by_cases hij : i = j
    · subst j
      ring_nf
      exact le_rfl
    · have hfactor : 0 ≤ (w i - w j)^2 := sq_nonneg _
      have h1 : A i j * (w i - w j)^2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (hA i j hij) hfactor
      nlinarith
  have hsum : ∑ i, ∑ j, (A i j * (w i)^2 + A i j * (w j)^2)
      ≤ ∑ i, ∑ j, 2 * (A i j * w i * w j) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    exact hpair i j
  have hfirst : ∑ i, ∑ j, A i j * (w i)^2 = ∑ i, (∑ j, A i j) * (w i)^2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_mul]
  have hsecond : ∑ i, ∑ j, A i j * (w j)^2 = ∑ i, (∑ j, A i j) * (w i)^2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    rw [← Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    exact (hsym i k).symm
  have hL : ∑ i, ∑ j, (A i j * (w i)^2 + A i j * (w j)^2)
      = 2 * (∑ i, (∑ j, A i j) * (w i)^2) := by
    calc
      ∑ i, ∑ j, (A i j * (w i)^2 + A i j * (w j)^2)
          = (∑ i, ∑ j, A i j * (w i)^2) + (∑ i, ∑ j, A i j * (w j)^2) := by
              simp_rw [Finset.sum_add_distrib]
      _ = (∑ i, (∑ j, A i j) * (w i)^2) + (∑ i, (∑ j, A i j) * (w i)^2) := by
              rw [hfirst, hsecond]
      _ = 2 * (∑ i, (∑ j, A i j) * (w i)^2) := by ring
  have hR : ∑ i, ∑ j, 2 * (A i j * w i * w j)
      = 2 * (∑ i, ∑ j, A i j * w i * w j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
  rw [hL, hR] at hsum
  linarith

theorem op223_zmatrix_posdef_of_positive_vector {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (v : ι → ℝ) (hsym : M.IsSymm)
    (hoff : ∀ i j, i ≠ j → M i j ≤ 0)
    (hv : ∀ i, 0 < v i) (hMv : ∀ i, 0 < (M.mulVec v) i) : M.PosDef := by
  have hHerm : M.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hsym
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hHerm ?_
  intro x hx
  rw [show star x = x from funext (fun i => by simp)]
  let w : ι → ℝ := fun i => x i / v i
  have hw : ∀ i, v i * w i = x i := by
    intro i
    dsimp [w]
    field_simp [ne_of_gt (hv i)]
  let A : ι → ι → ℝ := fun i j => v i * M i j * v j
  have hAsym : ∀ i j, A j i = A i j := by
    intro i j
    dsimp [A]
    rw [hsym.apply i j]
    ring
  have hAoff : ∀ i j, i ≠ j → A i j ≤ 0 := by
    intro i j hij
    dsimp [A]
    have h1 : v i * M i j ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hv i).le (hoff i j hij)
    exact mul_nonpos_of_nonpos_of_nonneg h1 (hv j).le
  have hineq := op223_zmatrix_posdef_of_positive_vector_sum_ineq A hAsym hAoff w
  have hrow : ∀ i, (∑ j, A i j) = v i * (M.mulVec v) i := by
    intro i
    dsimp [A]
    rw [Matrix.mulVec_apply]
    simp only [dotProduct, Matrix.row_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hSpos : 0 < ∑ i, (∑ j, A i j) * (w i)^2 := by
    simp_rw [hrow]
    apply Finset.sum_pos'
    · intro i hi
      exact mul_nonneg (mul_pos (hv i) (hMv i)).le (sq_nonneg (w i))
    · obtain ⟨k, hk⟩ := Function.ne_iff.mp hx
      refine ⟨k, Finset.mem_univ k, ?_⟩
      exact mul_pos (mul_pos (hv k) (hMv k))
        (sq_pos_of_ne_zero (div_ne_zero hk (ne_of_gt (hv k))))
  have hquad : x ⬝ᵥ M.mulVec x = ∑ i, ∑ j, A i j * w i * w j := by
    simp only [dotProduct]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Matrix.mulVec_apply]
    simp only [dotProduct, Matrix.row_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← hw i, ← hw j]
    dsimp [A]
    ring
  calc
    0 < ∑ i, (∑ j, A i j) * (w i)^2 := hSpos
    _ ≤ ∑ i, ∑ j, A i j * w i * w j := hineq
    _ = x ⬝ᵥ M.mulVec x := hquad.symm
