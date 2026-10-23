import AFTD.Prelude
import AFTD.Kb.Tcs.EvalMatrix3Triad
import AFTD.Kb.Tcs.Matrix3Triad

/-!
# eval_matrix3_triad_smul_right

Topic: algebraic_complexity   Node: c04f13d3aebf

Provenance: helper lemma. step towards matrix3_tensor_rank_int_le_22

Given a commutative semiring R, a triad t of type Matrix3Triad R, a scalar c : R, and matrices A and B, eval_matrix3_triad t A (c • B) equals c • eval_matrix3_triad t A B.
-/

/-- Scalar multiplication on the right factor of a triad evaluation pulls out as a scalar multiple of the whole evaluation matrix. -/
theorem eval_matrix3_triad_smul_right {R : Type*} [CommSemiring R] (t : Matrix3Triad R) (c : R) (A B : Matrix (Fin 3) (Fin 3) R) : eval_matrix3_triad t A (c • B) = c • eval_matrix3_triad t A B := by
  simp only [eval_matrix3_triad]
  have hsum : (∑ i, ∑ j, t.v i j * (c • B) i j) = c * ∑ i, ∑ j, t.v i j * B i j := by
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_left_comm]
  rw [hsum, smul_smul]
  congr 1
  ring
