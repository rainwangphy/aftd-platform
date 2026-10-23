import AFTD.Prelude
import AFTD.Kb.Tcs.EvalMatrix3Decomposition
import AFTD.Kb.Tcs.EvalMatrix3DecompositionAddRight
import AFTD.Kb.Tcs.Matrix3Triad
import AFTD.Kb.Tcs.EvalMatrix3Triad

/-!
# eval_matrix3_decomposition_sum_right

Topic: algebraic_complexity   Node: 1bac0589f923

Provenance: helper lemma. step towards matrix3_tensor_rank_int_le_22

Given a commutative semiring R, a finite set s, a list L of triads, a matrix A, and a family of matrices G, evaluating L on A and (∑ i ∈ s, G i) equals ∑ i ∈ s, eval_matrix3_decomposition L A (G i).
-/

/-- Evaluation of a triad decomposition distributes over finite sums in the right matrix argument. -/
theorem eval_matrix3_decomposition_sum_right {R : Type*} [CommSemiring R] {ι : Type*} (s : Finset ι) (L : List (Matrix3Triad R)) (A : Matrix (Fin 3) (Fin 3) R) (G : ι → Matrix (Fin 3) (Fin 3) R) : eval_matrix3_decomposition L A (∑ i ∈ s, G i) = ∑ i ∈ s, eval_matrix3_decomposition L A (G i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [eval_matrix3_decomposition, eval_matrix3_triad]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, eval_matrix3_decomposition_add_right, ih]
