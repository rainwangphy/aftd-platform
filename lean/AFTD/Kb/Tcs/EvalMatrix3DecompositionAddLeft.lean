import AFTD.Prelude
import AFTD.Kb.Tcs.EvalMatrix3Decomposition
import AFTD.Kb.Tcs.EvalMatrix3TriadAddLeft
import AFTD.Kb.Tcs.EvalMatrix3Triad
import AFTD.Kb.Tcs.Matrix3Triad

/-!
# eval_matrix3_decomposition_add_left

Topic: algebraic_complexity   Node: 5cd7b1481234

Provenance: helper lemma. step towards matrix3_tensor_rank_int_le_22

Given a commutative semiring R, a list L of Matrix3Triad R, and matrices A₁, A₂, and B, eval_matrix3_decomposition L (A₁ + A₂) B equals eval_matrix3_decomposition L A₁ B + eval_matrix3_decomposition L A₂ B.
-/

/-- Left-additivity of triad decomposition evaluation. -/
theorem eval_matrix3_decomposition_add_left {R : Type*} [CommSemiring R] (L : List (Matrix3Triad R)) (A₁ A₂ B : Matrix (Fin 3) (Fin 3) R) : eval_matrix3_decomposition L (A₁ + A₂) B = eval_matrix3_decomposition L A₁ B + eval_matrix3_decomposition L A₂ B := by
  induction L with
  | nil => simp [eval_matrix3_decomposition]
  | cons t L' ih =>
    simp [eval_matrix3_decomposition, eval_matrix3_triad_add_left]
    abel
