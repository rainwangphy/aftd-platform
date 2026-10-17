import AFTD.Prelude
import AFTD.Kb.Tcs.SingularValuesSorted
import AFTD.Kb.Tcs.SingularValues
import AFTD.Kb.Tcs.SingularValuesSortedZeroEqSup

/-!
# eigenvalue_le_singularValuesSorted_sq

Topic: quantum   Node: 4b049a6c404c

Provenance: formalization of a published result. Source: QuantumInfo, `eigenvalue_le_singularValuesSorted_sq`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Majorization.lean (Copyright (c) 2026 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

eigenvalue_le_singularValuesSorted_sq
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {d : Type*} [Fintype d] [DecidableEq d] in
lemma eigenvalue_le_singularValuesSorted_sq {e : Type*} [Fintype e] [DecidableEq e]
    (A : Matrix e e ℂ) (h : 0 < Fintype.card e) (i : e) :
  (isHermitian_mul_conjTranspose_self A.conjTranspose).eigenvalues i ≤
    (singularValuesSorted A ⟨0, h⟩) ^ 2 := by
  -- By definition of singular values, we know that $\sigma_i(A)^2 = \lambda_i(A^*A)$.
  have h_singular_value_squared : ∀ i, (singularValues A i) ^ 2 = (isHermitian_mul_conjTranspose_self A.conjTranspose).eigenvalues i := by
    intro i
    simp [singularValues]
    rw [Real.sq_sqrt (_)]
    convert Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i using 1
  rw [← h_singular_value_squared i]
  gcongr
  · exact Real.sqrt_nonneg _
  · convert singularValuesSorted_zero_eq_sup A h |> fun h => h.ge.trans' _
    exact Finset.le_sup' (fun i => singularValues A i) (Finset.mem_univ i)
