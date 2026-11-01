import AFTD.Prelude
import AFTD.Kb.Tcs.SpectralMinRe
import AFTD.Kb.Tcs.IsPositiveLinearMap
import AFTD.Kb.Tcs.IsTracePreservingLinearMap

/-!
# exists_positive_tp_violating_universal_spectral_bound

Topic: quantum   Node: 06a4f337b674

Provenance: original. Related work: OP-733: arXiv:2610.37187 (Removing Trace Preservation from a Universal Spectral Bound for 2-Positive Maps), Sec. 9, Concluding remarks: whether positive trace-preserving maps in dimension d >= 3 can violate (1.2), a question raised in arXiv:2506.02145.

For every d ≥ 3 there is a positive trace-preserving linear map Φ on d × d complex matrices with Tr(Φ) > d m(Φ) + d² − d. With a = (d−2)/(d−1), K = diag(a, a, 1, …, 1) and P the diagonal projection onto the first two coordinates, Φ(X) = K X K + (1 − a²) P Xᵀ P is positive (completely positive plus completely copositive) and trace-preserving, has operator trace (2a + d − 2)² + 2(1 − a²) and the eigenvalue 2a² − 1 (eigenvector E₁₂ − E₂₁); the trace exceeds d(2a² − 1) + d² − d by 2/(d − 1).
-/

/-- Diagonal weights: `a` on the first two coordinates, `1` elsewhere. -/
noncomputable def op733_k (d : ℕ) (a : ℝ) (i : Fin d) : ℂ := ((if i.val < 2 then a else 1 : ℝ) : ℂ)

/-- Indicator of the first two coordinates. -/
noncomputable def op733_p (d : ℕ) (i : Fin d) : ℂ := ((if i.val < 2 then 1 else 0 : ℝ) : ℂ)

/-- X ↦ K X K + (1 - a²) P Xᵀ P. -/
noncomputable def op733_gen (d : ℕ) (a : ℝ) :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ where
  toFun X := Matrix.diagonal (op733_k d a) * X * Matrix.diagonal (op733_k d a) +
    ((1 - a ^ 2 : ℝ) : ℂ) • (Matrix.diagonal (op733_p d) * X.transpose * Matrix.diagonal (op733_p d))
  map_add' X Y := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.transpose_add, smul_add]; abel
  map_smul' c X := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_smul, smul_add, RingHom.id_apply]
    rw [smul_comm c ((1 - a ^ 2 : ℝ) : ℂ)]

theorem op733_gen_apply (d : ℕ) (a : ℝ) (X : Matrix (Fin d) (Fin d) ℂ) : op733_gen d a X =
    Matrix.diagonal (op733_k d a) * X * Matrix.diagonal (op733_k d a) +
    ((1 - a ^ 2 : ℝ) : ℂ) • (Matrix.diagonal (op733_p d) * X.transpose * Matrix.diagonal (op733_p d)) := rfl

theorem op733_gen_entry (d : ℕ) (a : ℝ) (X : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    op733_gen d a X i j = op733_k d a i * X i j * op733_k d a j +
      ((1 - a ^ 2 : ℝ) : ℂ) * (op733_p d i * X j i * op733_p d j) := by
  simp [op733_gen_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]

open scoped ComplexOrder in
theorem op733_gen_pos (d : ℕ) (a : ℝ) (ha : a ^ 2 ≤ 1) : is_positive_linear_map d (op733_gen d a) := by
  classical
  intro X hX
  rw [op733_gen_apply]
  have hK : Matrix.conjTranspose (Matrix.diagonal (op733_k d a)) = Matrix.diagonal (op733_k d a) := by
    rw [Matrix.diagonal_conjTranspose]; congr 1; ext i; simp [op733_k]
  have hP : Matrix.conjTranspose (Matrix.diagonal (op733_p d)) = Matrix.diagonal (op733_p d) := by
    rw [Matrix.diagonal_conjTranspose]; congr 1; ext i; simp [op733_p]
  refine Matrix.PosSemidef.add ?_ (Matrix.PosSemidef.smul ?_ ?_)
  · have := hX.mul_mul_conjTranspose_same (Matrix.diagonal (op733_k d a))
    rwa [hK] at this
  · have := hX.transpose.mul_mul_conjTranspose_same (Matrix.diagonal (op733_p d))
    rwa [hP] at this
  · exact Complex.zero_le_real.mpr (by linarith)

theorem op733_gen_tp (d : ℕ) (a : ℝ) : is_trace_preserving_linear_map d (op733_gen d a) := by
  intro X
  simp only [Matrix.trace, Matrix.diag, op733_gen_entry]
  apply Finset.sum_congr rfl
  intro i _
  simp only [op733_k, op733_p]
  split_ifs <;> push_cast <;> ring

theorem op733_k_sum (n : ℕ) (a : ℝ) :
    ∑ i : Fin (n + 2), op733_k (n + 2) a i = ((2 * a + ((n + 2 : ℕ) - 2 : ℝ)) : ℂ) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  have h : ∀ i : Fin n, op733_k (n + 2) a i.succ.succ = 1 := by
    intro i; simp [op733_k, Fin.val_succ]
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  simp [op733_k]
  push_cast; ring

theorem op733_p_sum (n : ℕ) (c : ℂ) :
    ∑ i : Fin (n + 2), c * (op733_p (n + 2) i * op733_p (n + 2) i) = 2 * c := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  have h : ∀ i : Fin n, op733_p (n + 2) i.succ.succ = 0 := by
    intro i; simp [op733_p, Fin.val_succ]
  simp only [h, mul_zero, Finset.sum_const_zero, add_zero]
  simp [op733_p]
  ring

theorem op733_gen_trace (d : ℕ) (a : ℝ) (hd : 2 ≤ d) :
    (LinearMap.trace ℂ (Matrix (Fin d) (Fin d) ℂ)) (op733_gen d a) =
      ((2 * a + (d - 2) : ℝ) : ℂ) ^ 2 + 2 * ((1 - a ^ 2 : ℝ) : ℂ) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (Matrix.stdBasis ℂ (Fin d) (Fin d))]
  have hrepr : ∀ (M : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d),
      (Matrix.stdBasis ℂ (Fin d) (Fin d)).repr M (i, j) = M i j := fun _ _ _ => rfl
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, hrepr, op733_gen_entry,
    Matrix.stdBasis_eq_single, Fintype.sum_prod_type, Matrix.single_apply]
  simp only [and_self, ite_true, mul_one, one_mul]
  have hsplit : ∀ i j : Fin d, (if j = i ∧ i = j then (1 : ℂ) else 0) = if i = j then 1 else 0 := by
    intro i j; by_cases h : i = j <;> simp [h, eq_comm]
  simp only [hsplit, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_add_distrib]
  rw [← Finset.sum_mul_sum]
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 2 := ⟨d - 2, by omega⟩
  rw [op733_k_sum, op733_p_sum]; push_cast; ring

/-- The antisymmetric matrix unit on the first two coordinates. -/
noncomputable def op733_v (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => if i.val = 0 ∧ j.val = 1 then 1 else if i.val = 1 ∧ j.val = 0 then -1 else 0

theorem op733_gen_min_re_le (d : ℕ) (a : ℝ) (hd : 2 ≤ d) :
    spectral_min_re d (op733_gen d a) ≤ 2 * a ^ 2 - 1 := by
  have heig : op733_gen d a (op733_v d) = ((2 * a ^ 2 - 1 : ℝ) : ℂ) • op733_v d := by
    ext i j
    rw [op733_gen_entry]
    simp only [op733_v, op733_k, op733_p, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> first | (exfalso; omega) | (push_cast; ring)
  have hmem : ((2 * a ^ 2 - 1 : ℝ) : ℂ) ∈ spectrum ℂ (op733_gen d a) := by
    apply Module.End.HasEigenvalue.mem_spectrum
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := op733_v d)
    refine ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]; exact heig
    · intro h
      have := congrFun (congrFun h ⟨0, by omega⟩) ⟨1, by omega⟩
      simp [op733_v] at this
  unfold spectral_min_re
  have hfin : (Complex.re '' spectrum ℂ (op733_gen d a)).Finite :=
    (Module.End.finite_spectrum (op733_gen d a)).image _
  have := csInf_le hfin.bddBelow ⟨_, hmem, rfl⟩
  rwa [Complex.ofReal_re] at this

theorem exists_positive_tp_violating_universal_spectral_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ,
      is_positive_linear_map d Φ ∧ is_trace_preserving_linear_map d Φ ∧
      (d : ℝ) * spectral_min_re d Φ + (d : ℝ) ^ 2 - (d : ℝ) <
        ((LinearMap.trace ℂ (Matrix (Fin d) (Fin d) ℂ)) Φ).re := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  set a : ℝ := ((d : ℝ) - 2) / ((d : ℝ) - 1) with ha
  have h1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  have ha0 : 0 ≤ a := div_nonneg (by linarith) h1.le
  have ha1 : a ≤ 1 := (div_le_one h1).mpr (by linarith)
  refine ⟨op733_gen d a, op733_gen_pos d a (by nlinarith), op733_gen_tp d a, ?_⟩
  rw [op733_gen_trace d a (by omega)]
  have hm := op733_gen_min_re_le d a (by omega)
  have hre : (((2 * a + (d - 2) : ℝ) : ℂ) ^ 2 + 2 * ((1 - a ^ 2 : ℝ) : ℂ)).re =
      (2 * a + (d - 2)) ^ 2 + 2 * (1 - a ^ 2) := by
    rw [show (((2 * a + (d - 2) : ℝ) : ℂ) ^ 2 + 2 * ((1 - a ^ 2 : ℝ) : ℂ)) =
      (((2 * a + (d - 2)) ^ 2 + 2 * (1 - a ^ 2) : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_re _
  rw [hre]
  have hdm : (d : ℝ) * spectral_min_re d (op733_gen d a) ≤ (d : ℝ) * (2 * a ^ 2 - 1) :=
    mul_le_mul_of_nonneg_left hm (by linarith)
  have key : (d : ℝ) * (2 * a ^ 2 - 1) + (d : ℝ) ^ 2 - (d : ℝ) + 2 / ((d : ℝ) - 1) =
      (2 * a + (d - 2)) ^ 2 + 2 * (1 - a ^ 2) := by
    rw [ha]; field_simp; ring
  have hpos : 0 < 2 / ((d : ℝ) - 1) := div_pos (by norm_num) h1
  linarith
