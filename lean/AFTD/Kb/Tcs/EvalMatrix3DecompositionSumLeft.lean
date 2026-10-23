import AFTD.Prelude
import AFTD.Kb.Tcs.EvalMatrix3Decomposition
import AFTD.Kb.Tcs.EvalMatrix3DecompositionAddLeft
import AFTD.Kb.Tcs.Matrix3Triad
import AFTD.Kb.Tcs.EvalMatrix3Triad

/-!
# eval_matrix3_decomposition_sum_left

Topic: algebraic_complexity   Node: bab74e3fd384

Provenance: helper lemma. step towards matrix3_tensor_rank_int_le_22

Given a commutative semiring R, a finite set s, a list L of triads, a family of matrices F, and a matrix B, evaluating L on (∑ i ∈ s, F i) and B equals ∑ i ∈ s, eval_matrix3_decomposition L (F i) B.
-/

/-- Evaluation of a triad decomposition distributes over finite sums in the left matrix argument. -/
theorem eval_matrix3_decomposition_sum_left {R : Type*} [CommSemiring R] {ι : Type*} (s : Finset ι) (L : List (Matrix3Triad R)) (F : ι → Matrix (Fin 3) (Fin 3) R) (B : Matrix (Fin 3) (Fin 3) R) : eval_matrix3_decomposition L (∑ i ∈ s, F i) B = ∑ i ∈ s, eval_matrix3_decomposition L (F i) B := by
  -- `eval L · B` vanishes at `0`, so it is additive over finite sums of the left matrix.
  have hzero : ∀ L : List (Matrix3Triad R), eval_matrix3_decomposition L 0 B = 0 := by
    intro L
    induction L with
    | nil => simp [eval_matrix3_decomposition]
    | cons t L ih => simp [eval_matrix3_decomposition, eval_matrix3_triad]
  refine Finset.cons_induction (motive := fun s => eval_matrix3_decomposition L (∑ i ∈ s, F i) B = ∑ i ∈ s, eval_matrix3_decomposition L (F i) B) ?_ ?_ s
  · simp [hzero]
  · intro a s ha ih
    rw [Finset.sum_cons ha, eval_matrix3_decomposition_add_left, ih, Finset.sum_cons ha]
