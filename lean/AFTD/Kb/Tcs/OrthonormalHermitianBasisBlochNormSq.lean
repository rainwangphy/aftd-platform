import AFTD.Prelude
import AFTD.Kb.Tcs.HermitianMatrixParsevalSum
import AFTD.Kb.Tcs.IsOrthonormalHermitianBasis
import AFTD.Kb.Tcs.IsPureState
import AFTD.Kb.Tcs.QuadraticPureStateForm

/-!
# orthonormal_hermitian_basis_bloch_norm_sq

Topic: quantum   Node: 79105442000d

Provenance: helper lemma. step towards open_problem_qudit_pure_state_invariants

For any natural number d ≥ 1, any orthonormal Hermitian basis T, and any pure state ρ, the quadratic pure-state form with weight 1 equals (d - 1) / d.
-/

/-- For any natural number d ≥ 1, any orthonormal Hermitian basis T, and any pure state ρ, the quadratic pure-state form with weight 1 equals (d - 1) / d. -/
theorem orthonormal_hermitian_basis_bloch_norm_sq (d : ℕ) (hd : 1 ≤ d)
    (T : Fin (d^2 - 1) → Matrix (Fin d) (Fin d) ℂ) (hT : is_orthonormal_hermitian_basis d T)
    (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : is_pure_state ρ) :
    quadratic_pure_state_form T (fun _ => 1) ρ = ((d : ℝ) - 1) / (d : ℝ) := by
  have h := hermitian_matrix_parseval_sum d hd T hT ρ hρ.1
  simp only [quadratic_pure_state_form, one_mul]
  rw [h]
  obtain ⟨_, hsq, htr⟩ := hρ
  rw [hsq, htr]
  simp
  field_simp
