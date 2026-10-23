import AFTD.Prelude
import AFTD.Kb.Tcs.EvalMatrix3Decomposition
import AFTD.Kb.Tcs.EvalMatrix3TriadAddRight
import AFTD.Kb.Tcs.EvalMatrix3Triad
import AFTD.Kb.Tcs.Matrix3Triad

/-!
# eval_matrix3_decomposition_add_right

Topic: algebraic_complexity   Node: 372302856cb4

Provenance: helper lemma. step towards matrix3_tensor_rank_int_le_22

Given a commutative semiring R, a list L of Matrix3Triad R, and matrices A, B₁, and B₂, eval_matrix3_decomposition L A (B₁ + B₂) equals eval_matrix3_decomposition L A B₁ + eval_matrix3_decomposition L A B₂.
-/

/-- Right-additivity of triad decomposition evaluation. -/
theorem eval_matrix3_decomposition_add_right {R : Type*} [CommSemiring R] (L : List (Matrix3Triad R)) (A B₁ B₂ : Matrix (Fin 3) (Fin 3) R) : eval_matrix3_decomposition L A (B₁ + B₂) = eval_matrix3_decomposition L A B₁ + eval_matrix3_decomposition L A B₂ := by
  induction L with
  | nil => simp [eval_matrix3_decomposition]
  | cons t L' ih =>
    simp [eval_matrix3_decomposition, eval_matrix3_triad_add_right]
    abel
