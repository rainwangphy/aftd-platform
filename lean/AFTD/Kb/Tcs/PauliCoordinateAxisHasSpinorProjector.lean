import AFTD.Prelude
import AFTD.Kb.Tcs.PauliBlochMatrix

/-!
# pauli_coordinate_axis_has_spinor_projector

Topic: quantum   Node: 1e1039403787

Provenance: helper lemma. arXiv:2611.19367v1, Lemma 3, fixed coordinate-axis spinor.

For each signed coordinate direction, a two-component spinor has the corresponding rank-one Pauli projector.
-/

theorem pauli_coordinate_axis_has_spinor_projector (i : Fin 3) (δ : ℝ) (hδ : δ = 1 ∨ δ = -1) : ∃ u : Fin 2 → ℂ, ∀ s t, u s * star (u t) = (1 + pauli_bloch_matrix (Pi.single i δ)) s t / 2 := by
  fin_cases i
  · refine ⟨![((1+Complex.I)/2 : ℂ), ((δ:ℂ)*(1+Complex.I)/2 : ℂ)], ?_⟩
    rcases hδ with rfl | rfl
    · intro s t
      fin_cases s <;> fin_cases t <;>
        simp [pauli_bloch_matrix, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
        norm_num [Complex.ext_iff, Complex.I_mul_I]
    · intro s t
      fin_cases s <;> fin_cases t <;>
        simp [pauli_bloch_matrix, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
        norm_num [Complex.ext_iff, Complex.I_mul_I]
  · refine ⟨![((1+Complex.I)/2 : ℂ), (-(δ:ℂ)*(1-Complex.I)/2 : ℂ)], ?_⟩
    rcases hδ with rfl | rfl
    · intro s t
      fin_cases s <;> fin_cases t <;>
        simp [pauli_bloch_matrix, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
        norm_num [Complex.ext_iff, Complex.I_mul_I]
    · intro s t
      fin_cases s <;> fin_cases t <;>
        simp [pauli_bloch_matrix, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
        norm_num [Complex.ext_iff, Complex.I_mul_I]
  · refine ⟨![(((1+δ)/2 : ℝ) : ℂ), (((1-δ)/2 : ℝ) : ℂ)], ?_⟩
    rcases hδ with rfl | rfl
    · intro s t
      fin_cases s <;> fin_cases t <;>
        simp [pauli_bloch_matrix, Matrix.cons_val_zero, Matrix.cons_val_one]
    · intro s t
      fin_cases s <;> fin_cases t <;>
        simp [pauli_bloch_matrix, Matrix.cons_val_zero, Matrix.cons_val_one]
