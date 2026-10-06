import AFTD.Prelude
import AFTD.Kb.Tcs.CliffordTGateMatrix

/-!
# clifford_t_gate_matrix_t_sq

Topic: quantum   Node: 11f9516bddd2

Provenance: original.

Sanity check: T^2 = S on every qubit.
-/

theorem clifford_t_gate_matrix_t_sq {N : ℕ} (i : Fin N) : clifford_t_gate_matrix (.t i) * clifford_t_gate_matrix (.t i) = clifford_t_gate_matrix (.s i) := by
  dsimp [clifford_t_gate_matrix]
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  ext x
  split_ifs with h
  · rw [← Complex.exp_add]
    have h1 : (Real.pi / 4 * Complex.I : ℂ) + Real.pi / 4 * Complex.I = Real.pi / 2 * Complex.I := by
      ring
    rw [h1, Complex.exp_pi_div_two_mul_I]
  · ring
