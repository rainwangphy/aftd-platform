import AFTD.Prelude
import AFTD.Kb.Tcs.EvalMatrix3Decomposition
import AFTD.Kb.Tcs.EvalMatrix3Triad
import AFTD.Kb.Tcs.Matrix3Triad

/-!
# eval_matrix3_decomposition_apply

Topic: algebraic_complexity   Node: 8d454f739fbe

Entry (i, j) of the evaluation of a list of 3x3 triads on A and B is the sum, over the triads, of (sum of u_kl A_kl) times (sum of v_kl B_kl) times w_ij.
-/

theorem eval_matrix3_decomposition_apply {R : Type*} [CommSemiring R] (L : List (Matrix3Triad R)) (A B : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3) : eval_matrix3_decomposition L A B i j = (L.map fun t => (∑ k : Fin 3, ∑ l : Fin 3, t.u k l * A k l) * (∑ k : Fin 3, ∑ l : Fin 3, t.v k l * B k l) * t.w i j).sum := by
  induction L with
  | nil => simp [eval_matrix3_decomposition]
  | cons t L ih =>
    simp only [eval_matrix3_decomposition, List.map_cons, List.sum_cons, Matrix.add_apply] at ih ⊢
    rw [ih]
    simp [eval_matrix3_triad, smul_eq_mul]
