import AFTD.Prelude
import AFTD.Kb.Tcs.SingularValuesSorted
import AFTD.Kb.Tcs.IsHermitianInnerLeSupEigenvalueMulInner
import AFTD.Kb.Tcs.EigenvalueLeSingularValuesSortedSq

/-!
# quadratic_form_le_singularValuesSorted_sq

Topic: quantum   Node: 6f31f49fbd98

Provenance: formalization of a published result. Source: QuantumInfo, `quadratic_form_le_singularValuesSorted_sq`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Majorization.lean (Copyright (c) 2026 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The quadratic form of `A† A` is bounded by (max singular value)² * ‖v‖².
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {d : Type*} [Fintype d] [DecidableEq d] in
/-- The quadratic form of `A† A` is bounded by (max singular value)² * ‖v‖². -/
lemma quadratic_form_le_singularValuesSorted_sq {e : Type*} [Fintype e] [DecidableEq e]
    (A : Matrix e e ℂ) (h : 0 < Fintype.card e) (v : e → ℂ) :
  Complex.re (star v ⬝ᵥ (A.conjTranspose * A).mulVec v) ≤
    (singularValuesSorted A ⟨0, h⟩) ^ 2 * Complex.re (star v ⬝ᵥ v) := by
  apply le_trans (IsHermitian.inner_le_sup_eigenvalue_mul_inner (Aᴴ * A) (by
    simp [Matrix.IsHermitian]) h v)
  apply_rules [mul_le_mul_of_nonneg_right, Finset.sup'_le]
  · intro i _
    convert! eigenvalue_le_singularValuesSorted_sq A h i using 1
    simp [Matrix.conjTranspose_conjTranspose]
  · simp [dotProduct]
    exact Finset.sum_nonneg fun _ _ => add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
