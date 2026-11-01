import AFTD.Prelude
import AFTD.Kb.Tcs.SpectralMinRe
import AFTD.Kb.Tcs.IsPositiveLinearMap
import AFTD.Kb.Tcs.IsTracePreservingLinearMap

/-!
# not_universal_spectral_bound_positive_tp_dim_three

Topic: quantum   Node: 579642087cf4

Provenance: original. Related work: OP-733: arXiv:2610.37187 (Removing Trace Preservation from a Universal Spectral Bound for 2-Positive Maps), Sec. 9, Concluding remarks: whether positive trace-preserving maps in dimension d >= 3 can violate (1.2), a question raised in arXiv:2506.02145.

The universal spectral bound Tr(Φ) ≤ 3 m(Φ) + 6 fails for some positive trace-preserving map Φ on 3 × 3 complex matrices: Φ(X) = K X K + (3/4) P Xᵀ P with K = diag(1/2, 1/2, 1) and P = diag(1, 1, 0) is positive (a completely positive plus a completely copositive map) and trace-preserving, has operator trace 11/2 and the eigenvalue -1/2 (eigenvector E₁₂ - E₂₁), so 3 m(Φ) + 6 ≤ 9/2 < 11/2.
-/

/-- The map X ↦ K X K + (3/4) P Xᵀ P on 3 × 3 complex matrices, K = diag(1/2, 1/2, 1), P = diag(1, 1, 0). -/
noncomputable def op733_map : Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] Matrix (Fin 3) (Fin 3) ℂ where
  toFun X := Matrix.diagonal ![1/2, 1/2, 1] * X * Matrix.diagonal ![1/2, 1/2, 1] +
    (3/4 : ℂ) • (Matrix.diagonal ![1, 1, 0] * X.transpose * Matrix.diagonal ![1, 1, 0])
  map_add' X Y := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.transpose_add, smul_add]; abel
  map_smul' c X := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_smul, smul_add, RingHom.id_apply]
    rw [smul_comm c (3/4 : ℂ)]

theorem op733_map_apply (X : Matrix (Fin 3) (Fin 3) ℂ) : op733_map X =
    Matrix.diagonal ![1/2, 1/2, 1] * X * Matrix.diagonal ![1/2, 1/2, 1] +
    (3/4 : ℂ) • (Matrix.diagonal ![1, 1, 0] * X.transpose * Matrix.diagonal ![1, 1, 0]) := rfl

open scoped ComplexOrder in
theorem op733_pos : is_positive_linear_map 3 op733_map := by
  classical
  intro X hX
  rw [op733_map_apply]
  have hK : Matrix.conjTranspose (Matrix.diagonal ![(1/2 : ℂ), 1/2, 1]) = Matrix.diagonal ![1/2, 1/2, 1] := by
    rw [Matrix.diagonal_conjTranspose]; congr 1; ext i; fin_cases i <;> simp
  have hP : Matrix.conjTranspose (Matrix.diagonal ![(1 : ℂ), 1, 0]) = Matrix.diagonal ![1, 1, 0] := by
    rw [Matrix.diagonal_conjTranspose]; congr 1; ext i; fin_cases i <;> simp
  refine Matrix.PosSemidef.add ?_ (Matrix.PosSemidef.smul ?_ ?_)
  · have := hX.mul_mul_conjTranspose_same (Matrix.diagonal ![(1/2 : ℂ), 1/2, 1])
    rwa [hK] at this
  · have := hX.transpose.mul_mul_conjTranspose_same (Matrix.diagonal ![(1 : ℂ), 1, 0])
    rwa [hP] at this
  · rw [show (3/4 : ℂ) = ((3/4 : ℝ) : ℂ) by push_cast; ring]
    exact Complex.zero_le_real.mpr (by norm_num)

theorem op733_tp : is_trace_preserving_linear_map 3 op733_map := by
  intro X
  rw [op733_map_apply]
  simp [Matrix.trace, Fin.sum_univ_three, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

theorem op733_eigen : op733_map (Matrix.of ![![0, 1, 0], ![-1, 0, 0], ![0, 0, 0]]) =
    (-1/2 : ℂ) • Matrix.of ![![0, 1, 0], ![-1, 0, 0], ![0, 0, 0]] := by
  rw [op733_map_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transpose_apply] <;> norm_num

theorem op733_min_re_le : spectral_min_re 3 op733_map ≤ -1/2 := by
  have hmem : (-1/2 : ℂ) ∈ spectrum ℂ op733_map := by
    apply Module.End.HasEigenvalue.mem_spectrum
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := Matrix.of ![![0, 1, 0], ![-1, 0, 0], ![0, 0, 0]])
    refine ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]; exact op733_eigen
    · intro h
      have := congrFun (congrFun h 0) 1
      simp at this
  unfold spectral_min_re
  have hfin : (Complex.re '' spectrum ℂ op733_map).Finite :=
    (Module.End.finite_spectrum op733_map).image _
  have := csInf_le hfin.bddBelow ⟨_, hmem, rfl⟩
  simpa using this

theorem op733_repr_a (M : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3) :
    (Matrix.stdBasis ℂ (Fin 3) (Fin 3)).repr M (i, j) = M i j := rfl

theorem op733_trace : (LinearMap.trace ℂ (Matrix (Fin 3) (Fin 3) ℂ)) op733_map = 11/2 := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (Matrix.stdBasis ℂ (Fin 3) (Fin 3))]
  simp [Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_three, LinearMap.toMatrix_apply,
    op733_map_apply, Matrix.stdBasis_eq_single, Matrix.diagonal_mul, Matrix.mul_diagonal, op733_repr_a,
    Matrix.single_apply]
  norm_num

theorem not_universal_spectral_bound_positive_tp_dim_three :
    ¬ ∀ (Φ : Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] Matrix (Fin 3) (Fin 3) ℂ),
      is_positive_linear_map 3 Φ → is_trace_preserving_linear_map 3 Φ →
      ((LinearMap.trace ℂ (Matrix (Fin 3) (Fin 3) ℂ)) Φ).re ≤ 3 * spectral_min_re 3 Φ + 6 := by
  intro h
  have h1 := h op733_map op733_pos op733_tp
  rw [op733_trace] at h1
  have h2 := op733_min_re_le
  norm_num at h1
  linarith
