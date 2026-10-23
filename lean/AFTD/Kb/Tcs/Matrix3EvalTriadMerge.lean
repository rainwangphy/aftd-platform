import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3Triad
import AFTD.Kb.Tcs.EvalMatrix3Triad

/-!
# matrix3_eval_triad_merge

Topic: algebraic_complexity   Node: fee390d5ec2e

Provenance: helper lemma. step towards matrix3_tensor_rank_zmod2_le_22

Two triads that agree in two of their three slots can be replaced by a single triad: if they share u and w their v's add, if they share v and w their u's add, and if they share u and v their w's add — in each case the sum of the two evaluations equals the evaluation of the merged triad, for all A and B.
-/

/-- The three merge identities for triads: two triads agreeing in two slots have the evaluation of the triad obtained by adding the remaining slots. -/
theorem matrix3_eval_triad_merge {R : Type*} [CommSemiring R]
    (u₁ u₂ v₁ v₂ w₁ w₂ : Matrix (Fin 3) (Fin 3) R) (A B : Matrix (Fin 3) (Fin 3) R) :
    (eval_matrix3_triad ⟨u₁, v₁, w₁⟩ A B + eval_matrix3_triad ⟨u₁, v₂, w₁⟩ A B
        = eval_matrix3_triad ⟨u₁, v₁ + v₂, w₁⟩ A B) ∧
    (eval_matrix3_triad ⟨u₁, v₁, w₁⟩ A B + eval_matrix3_triad ⟨u₂, v₁, w₁⟩ A B
        = eval_matrix3_triad ⟨u₁ + u₂, v₁, w₁⟩ A B) ∧
    (eval_matrix3_triad ⟨u₁, v₁, w₁⟩ A B + eval_matrix3_triad ⟨u₁, v₁, w₂⟩ A B
        = eval_matrix3_triad ⟨u₁, v₁, w₁ + w₂⟩ A B) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [eval_matrix3_triad, Matrix.add_apply, add_mul, mul_add,
      Finset.sum_add_distrib, add_smul, smul_add]
