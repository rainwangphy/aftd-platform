import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3Triad
import AFTD.Kb.Tcs.EvalMatrix3Triad

/-!
# matrix3_eval_triad_zero_v

Topic: algebraic_complexity   Node: 15e22dcf455e

Provenance: helper lemma. step towards matrix3_tensor_rank_int_le_22

Evaluating any triad whose v component is zero yields the zero matrix for all input matrices A and B.
-/

/-- Evaluating any triad whose v component is zero yields the zero matrix for all input matrices A and B. -/
theorem matrix3_eval_triad_zero_v {R : Type*} [CommSemiring R] (u w : Matrix (Fin 3) (Fin 3) R) (A B : Matrix (Fin 3) (Fin 3) R) :
    eval_matrix3_triad ⟨u, 0, w⟩ A B = 0 := by
  simp [eval_matrix3_triad]
