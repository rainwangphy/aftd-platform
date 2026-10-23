import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3Triad
import AFTD.Kb.Tcs.EvalMatrix3Triad

/-!
# matrix3_eval_triad_add_self_of_two_eq_zero

Topic: algebraic_complexity   Node: cac364acc9ec

Provenance: helper lemma. step towards matrix3_tensor_rank_zmod2_le_22

In characteristic 2 a triad repeated twice contributes nothing: if 2 = 0 in R then eval t A B + eval t A B = 0 for every triad t and all matrices A, B.
-/

/-- Over a ring of characteristic 2, a triad counted twice cancels; combined with the merge identity this shows a shortest decomposition never repeats a triad. -/
theorem matrix3_eval_triad_add_self_of_two_eq_zero {R : Type*} [CommRing R] (h2 : (2 : R) = 0)
    (t : Matrix3Triad R) (A B : Matrix (Fin 3) (Fin 3) R) :
    eval_matrix3_triad t A B + eval_matrix3_triad t A B = 0 := by
  simp only [eval_matrix3_triad]
  rw [← add_smul, ← two_mul, h2, zero_mul, zero_smul]
