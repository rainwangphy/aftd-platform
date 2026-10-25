import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3Triad
import AFTD.Kb.Tcs.EvalMatrix3Triad

/-!
# matrix3_eval_triad_zero_u

Topic: algebraic_complexity   Node: d7a5e3305d7b

Provenance: helper lemma. step towards matrix3_tensor_rank_int_le_22

Evaluating any triad whose u component is zero yields the zero matrix for all input matrices A and B.
-/

/-- Evaluating any triad whose u component is zero yields the zero matrix for all input matrices A and B. -/
theorem matrix3_eval_triad_zero_u {R : Type*} [CommSemiring R] (v w : Matrix (Fin 3) (Fin 3) R) (A B : Matrix (Fin 3) (Fin 3) R) :
    eval_matrix3_triad ⟨0, v, w⟩ A B = 0 := by
  simp [eval_matrix3_triad]
