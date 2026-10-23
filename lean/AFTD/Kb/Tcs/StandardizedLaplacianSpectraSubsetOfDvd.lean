import AFTD.Prelude
import AFTD.Kb.Tcs.IsStandardizedLaplacian
import AFTD.Kb.Tcs.StandardizedLaplacianSpectra
import AFTD.Kb.Tcs.BalancedBlowupMatrix
import AFTD.Kb.Tcs.BalancedBlowupMatrixRowSum
import AFTD.Kb.Tcs.BalancedBlowupMatrixOffDiag
import AFTD.Kb.Tcs.BalancedBlowupSpectrumSubset

/-!
# standardized_laplacian_spectra_subset_of_dvd

Topic: graphs   Node: 2a54ee6f90cc

Provenance: formalization of a published result. Source: scout/2610-14100-digraph-laplacian-spectra-the-2005-polygon-conjecture-fails.md:1044

Let m, n ≥ 2 be natural numbers such that m divides n. Then the set of eigenvalues of standardized Laplacian matrices of order m is a subset of the set of eigenvalues of standardized Laplacian matrices of order n.
-/

/-- If m divides n for integers m, n >= 2, then Lambda_m is a subset of Lambda_n. -/
theorem standardized_laplacian_spectra_subset_of_dvd (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hdvd : m ∣ n) :
    standardized_laplacian_spectra m ⊆ standardized_laplacian_spectra n := by
  intro z hz
  simp only [standardized_laplacian_spectra] at hz ⊢
  rcases hz with ⟨L, hL, hzL⟩
  rcases hL with ⟨hL_row, hL_off⟩
  set d := n / m with hd_def
  have hm1 : 1 ≤ m := by omega
  have hd : 1 ≤ d := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) (by omega)
  have h_mul : m * d = n := Nat.mul_div_cancel' hdvd
  set L' := balanced_blowup_matrix m d L with hL'_def
  have hzL' : z ∈ spectrum ℂ (L'.map Complex.ofReal) :=
    balanced_blowup_spectrum_subset m d hd L hzL
  let e : Fin m × Fin d ≃ Fin n := finProdFinEquiv.trans (finCongr h_mul)
  set M := Matrix.reindex e e L' with hM_def
  use M
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i
    change ∑ j : Fin n, Matrix.reindex e e L' i j = 0
    rw [← Equiv.sum_comp e (fun j => Matrix.reindex e e L' i j)]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rcases e.symm i with ⟨i₁, s₁⟩
    rw [Fintype.sum_prod_type]
    exact balanced_blowup_matrix_row_sum m d hd L hL_row i₁ s₁
  · intro i j hij
    change -(1 : ℝ) / (n : ℝ) ≤ Matrix.reindex e e L' i j ∧ Matrix.reindex e e L' i j ≤ 0
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    have hne : e.symm i ≠ e.symm j := by
      intro h
      apply hij
      exact e.symm.injective h
    have h_off := balanced_blowup_matrix_off_diag m d hm1 hd L hL_off (e.symm i).1 (e.symm j).1 (e.symm i).2 (e.symm j).2 hne
    have h_cast : (n : ℝ) = (m * d : ℝ) := by rw [← h_mul]; push_cast; rfl
    rw [h_cast]
    exact h_off
  · have h_map : M.map Complex.ofReal = Matrix.reindexAlgEquiv ℂ ℂ e (L'.map Complex.ofReal) := by
      rw [hM_def]
      ext i j
      simp [Matrix.coe_reindexAlgEquiv]
    rw [h_map]
    rw [AlgEquiv.spectrum_eq (Matrix.reindexAlgEquiv ℂ ℂ e) (L'.map Complex.ofReal)]
    exact hzL'
