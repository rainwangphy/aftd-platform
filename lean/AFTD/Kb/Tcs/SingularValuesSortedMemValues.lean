import AFTD.Prelude
import AFTD.Kb.Tcs.SingularValuesSorted
import AFTD.Kb.Tcs.SingularValues

/-!
# singularValuesSorted_mem_values

Topic: quantum   Node: 541f9f992733

Provenance: formalization of a published result. Source: QuantumInfo, `singularValuesSorted_mem_values`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Majorization.lean (Copyright (c) 2026 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Each sorted singular value appears among the original singular values.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {d : Type*} [Fintype d] [DecidableEq d] in
/-- Each sorted singular value appears among the original singular values. -/
lemma singularValuesSorted_mem_values {e : Type*} [Fintype e] [DecidableEq e]
    (A : Matrix e e ℂ) (j : Fin (Fintype.card e)) :
    ∃ i : e, singularValuesSorted A j = singularValues A i := by
  have h_mem : singularValuesSorted A j ∈ Multiset.sort (Finset.univ.val.map (singularValues A)) (· ≥ ·) := by
    simp [singularValuesSorted]
  rw [Multiset.mem_sort] at h_mem
  simp at h_mem
  obtain ⟨i, hi⟩ := h_mem
  exact ⟨i, hi.symm⟩
