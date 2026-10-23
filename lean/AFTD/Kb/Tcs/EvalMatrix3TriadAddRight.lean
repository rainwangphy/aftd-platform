import AFTD.Prelude
import AFTD.Kb.Tcs.EvalMatrix3Triad
import AFTD.Kb.Tcs.Matrix3Triad

/-!
# eval_matrix3_triad_add_right

Topic: algebraic_complexity   Node: d86d72fd76ac

Provenance: helper lemma. step towards matrix3_tensor_rank_int_le_22

Given a commutative semiring R, a triad t of type Matrix3Triad R, and matrices A, B₁, and B₂ in Matrix (Fin 3) (Fin 3) R, eval_matrix3_triad t A (B₁ + B₂) equals eval_matrix3_triad t A B₁ + eval_matrix3_triad t A B₂.
-/

/-- Right-additivity of triad evaluation: eval_matrix3_triad t A (B₁ + B₂) = eval_matrix3_triad t A B₁ + eval_matrix3_triad t A B₂. -/
theorem eval_matrix3_triad_add_right {R : Type*} [CommSemiring R] (t : Matrix3Triad R) (A B₁ B₂ : Matrix (Fin 3) (Fin 3) R) : eval_matrix3_triad t A (B₁ + B₂) = eval_matrix3_triad t A B₁ + eval_matrix3_triad t A B₂ := by
  unfold eval_matrix3_triad
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, add_smul]
