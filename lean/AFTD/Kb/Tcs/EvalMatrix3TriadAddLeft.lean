import AFTD.Prelude
import AFTD.Kb.Tcs.EvalMatrix3Triad
import AFTD.Kb.Tcs.Matrix3Triad

/-!
# eval_matrix3_triad_add_left

Topic: algebraic_complexity   Node: 5492e0d3d725

Provenance: helper lemma. step towards matrix3_tensor_rank_int_le_22

Given a commutative semiring R, a triad t of type Matrix3Triad R, and matrices A₁, A₂, and B in Matrix (Fin 3) (Fin 3) R, eval_matrix3_triad t (A₁ + A₂) B equals eval_matrix3_triad t A₁ B + eval_matrix3_triad t A₂ B.
-/

/-- Evaluation of a 3x3 triad is additive in its first matrix argument. -/
theorem eval_matrix3_triad_add_left {R : Type*} [CommSemiring R] (t : Matrix3Triad R) (A₁ A₂ B : Matrix (Fin 3) (Fin 3) R) : eval_matrix3_triad t (A₁ + A₂) B = eval_matrix3_triad t A₁ B + eval_matrix3_triad t A₂ B := by
  simp only [eval_matrix3_triad, Matrix.add_apply, Finset.sum_add_distrib, mul_add, add_mul,
    add_smul]
