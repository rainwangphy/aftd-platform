import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3Triad
import AFTD.Kb.Tcs.EvalMatrix3Triad

/-!
# matrix3_eval_triad_zero_w

Topic: algebraic_complexity   Node: 87e0b330ac7c

Provenance: helper lemma. step towards matrix3_tensor_rank_int_le_22

Evaluating any triad whose w component is zero yields the zero matrix for all input matrices A and B.
-/

/-- A triad with zero w component evaluates to zero everywhere. -/
theorem matrix3_eval_triad_zero_w {R : Type*} [CommSemiring R] (u v : Matrix (Fin 3) (Fin 3) R) (A B : Matrix (Fin 3) (Fin 3) R) :
    eval_matrix3_triad ⟨u, v, 0⟩ A B = 0 := by
  simp [eval_matrix3_triad]
