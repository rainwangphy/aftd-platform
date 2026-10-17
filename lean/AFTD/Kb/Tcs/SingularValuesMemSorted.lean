import AFTD.Prelude
import AFTD.Kb.Tcs.SingularValues
import AFTD.Kb.Tcs.SingularValuesSorted

/-!
# singularValues_mem_sorted

Topic: quantum   Node: 9d719ce64de5

Provenance: formalization of a published result. Source: QuantumInfo, `singularValues_mem_sorted`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Majorization.lean (Copyright (c) 2026 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Each singular value appears in the sorted list.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {d : Type*} [Fintype d] [DecidableEq d] in
/-- Each singular value appears in the sorted list. -/
lemma singularValues_mem_sorted {e : Type*} [Fintype e] [DecidableEq e]
    (A : Matrix e e ℂ) (i : e) :
    ∃ j : Fin (Fintype.card e), singularValues A i = singularValuesSorted A j := by
  have h_mem : singularValues A i ∈ Multiset.sort (Finset.univ.val.map (singularValues A)) (· ≥ ·) := by
    simp [Multiset.mem_sort]
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h_mem
  exact ⟨⟨j, by simpa using j.2⟩, hj.symm⟩
