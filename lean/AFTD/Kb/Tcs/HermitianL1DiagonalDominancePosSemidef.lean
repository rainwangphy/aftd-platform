import AFTD.Prelude

/-!
# hermitian_l1_diagonal_dominance_pos_semidef

Topic: quantum   Node: cc31dbc6da18

Provenance: helper lemma. Standard Hermitian diagonal-dominance criterion via eigenvalue localization.

A finite Hermitian complex matrix is positive semidefinite when each diagonal entry dominates the sum of the absolute real and imaginary parts of the off-diagonal entries in its row.
-/

open scoped ComplexOrder
open WithLp

theorem hermitian_l1_diagonal_dominance_pos_semidef
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (hA : A.IsHermitian)
    (hdom : ∀ i, (∑ j ∈ Finset.univ.erase i, (|(A i j).re| + |(A i j).im|)) ≤ (A i i).re) :
    A.PosSemidef := by
  set_option maxHeartbeats 4000000 in
    classical
    rw [hA.posSemidef_iff_eigenvalues_nonneg]
    intro i
    change 0 ≤ hA.eigenvalues i
    let v : n → ℂ := ⇑(hA.eigenvectorBasis i)
    have hv : v ≠ 0 := (ofLp_eq_zero 2).ne.2 (hA.eigenvectorBasis.orthonormal.ne_zero i)
    have heq : Matrix.toLin' A v = ((hA.eigenvalues i : ℝ) : ℂ) • v := by
      rw [Matrix.toLin'_apply]
      simpa [v, RCLike.real_smul_eq_coe_smul] using hA.mulVec_eigenvectorBasis i
    have hev : Module.End.HasEigenvalue (Matrix.toLin' A) ((hA.eigenvalues i : ℝ) : ℂ) := by
      apply Module.End.hasEigenvalue_of_hasEigenvector
      exact ⟨Module.End.mem_eigenspace_iff.mpr heq,hv⟩
    obtain ⟨j,hball⟩ := eigenvalue_mem_ball hev
    have hnorm : ‖((hA.eigenvalues i : ℝ) : ℂ) - A j j‖ ≤ ∑ l ∈ Finset.univ.erase j, ‖A j l‖ := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hball
    have hsum : (∑ l ∈ Finset.univ.erase j, ‖A j l‖) ≤
        ∑ l ∈ Finset.univ.erase j, (|(A j l).re| + |(A j l).im|) := by
      apply Finset.sum_le_sum
      intro l hl
      exact Complex.norm_le_abs_re_add_abs_im _
    have hre := Complex.abs_re_le_norm (((hA.eigenvalues i : ℝ) : ℂ) - A j j)
    have hbound : |hA.eigenvalues i - (A j j).re| ≤ (A j j).re := by
      have hh := hdom j
      simp only [Complex.sub_re, Complex.ofReal_re] at hre
      linarith
    have hneg : -(hA.eigenvalues i - (A j j).re) ≤ |hA.eigenvalues i - (A j j).re| := neg_le_abs _
    linarith
