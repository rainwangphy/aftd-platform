import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3ValidOfUnitChecks
import AFTD.Kb.Tcs.EvalMatrix3DecompositionApply
import AFTD.Kb.Tcs.Matrix3Triad
import AFTD.Kb.Tcs.EvalMatrix3Decomposition
import AFTD.Kb.Tcs.IsValidMatrix3Decomposition

/-!
# matrix3_valid_iff_trace_tensor_identity

Topic: algebraic_complexity   Node: 1b8ca3c036be

Provenance: helper lemma. Adapter for OP-2 / matrix3_tensor_rank_zmod2_le_22; cyclic trace coefficient convention in arXiv:2610.11823v3, Section 2 and its companion RootSound/Tensor.lean. Proof written here using the existing unit-check extension theorem; no external proof is assumed.

For a finite indexed family of triads over any commutative semiring, validity of the decomposition whose output weights are the transposes of c is equivalent to the coefficient identities of the cyclic trace tensor. This identifies the bilinear map convention with the tensor convention used in arXiv:2610.11823.
-/

open Matrix
private theorem matrix3_trace_eval_units {R : Type*} [CommSemiring R] (n : ℕ)
    (a b c : Fin n → Matrix (Fin 3) (Fin 3) R) (i j k l p q : Fin 3) :
    eval_matrix3_decomposition (List.ofFn fun s => (⟨a s, b s, (c s)ᵀ⟩ : Matrix3Triad R))
      (Matrix.single i j 1) (Matrix.single k l 1) p q =
        ∑ s, a s i j * b s k l * c s q p := by
  rw [eval_matrix3_decomposition_apply]
  simp [List.map_ofFn, List.sum_ofFn, Matrix.single_apply, Matrix.transpose_apply, ite_and]

private theorem matrix3_trace_product_units {R : Type*} [CommSemiring R]
    (i j j' k k' i' : Fin 3) :
    (Matrix.single i j (1 : R) * Matrix.single j' k 1 : Matrix (Fin 3) (Fin 3) R) i' k' =
      if j = j' ∧ k = k' ∧ i = i' then 1 else 0 := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and]
  split_ifs <;> simp_all

theorem matrix3_valid_iff_trace_tensor_identity {R : Type*} [CommSemiring R]
    (n : ℕ) (a b c : Fin n → Matrix (Fin 3) (Fin 3) R) :
    is_valid_matrix3_decomposition
      (List.ofFn fun s => (⟨a s, b s, (c s)ᵀ⟩ : Matrix3Triad R)) ↔
    ∀ i j j' k k' i' : Fin 3,
      ∑ s, a s i j * b s j' k * c s k' i' =
        if j = j' ∧ k = k' ∧ i = i' then 1 else 0 := by
  constructor
  · intro h i j j' k k' i'
    have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M i' k')
      (h (Matrix.single i j 1) (Matrix.single j' k 1))
    rw [matrix3_trace_eval_units, matrix3_trace_product_units] at he
    exact he
  · intro h
    apply matrix3_valid_of_unit_checks
    intro i j j' k
    ext i' k'
    rw [matrix3_trace_eval_units, matrix3_trace_product_units]
    exact h i j j' k k' i'
