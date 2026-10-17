import AFTD.Prelude
import AFTD.Kb.Tcs.SingularValuesSorted
import AFTD.Kb.Tcs.SingularValues
import AFTD.Kb.Tcs.SingularValuesSortedAntitone

/-!
# singularValuesSorted_zero_eq_sup

Topic: quantum   Node: 58839a7dbf4b

Provenance: formalization of a published result. Source: QuantumInfo, `singularValuesSorted_zero_eq_sup`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Majorization.lean (Copyright (c) 2026 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The 0th sorted singular value is the maximum of the singular values.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {d : Type*} [Fintype d] [DecidableEq d] in
/-- The 0th sorted singular value is the maximum of the singular values. -/
lemma singularValuesSorted_zero_eq_sup {e : Type*} [Fintype e] [DecidableEq e]
    (A : Matrix e e ℂ) (h : 0 < Fintype.card e) :
    singularValuesSorted A ⟨0, h⟩ = Finset.sup' Finset.univ
      (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp h))
      (singularValues A) := by
  refine' le_antisymm _ _
  · -- Since the list is sorted in decreasing order, every element in the list is less than or equal to the supremum of the original set.
    have h_le_sup : ∀ x ∈ Multiset.sort (Multiset.map (singularValues A) Finset.univ.val) (· ≥ ·), x ≤ Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨Classical.choose (Finset.card_pos.mp h)⟩) (singularValues A) := by
      aesop
    exact h_le_sup _ (by simp [singularValuesSorted])
  · have h_max_le_ge : ∀ i, singularValues A i ≤ singularValuesSorted A ⟨0, h⟩ := by
      intro i
      have h_max_le_ge : ∀ j, singularValuesSorted A j ≤ singularValuesSorted A ⟨0, h⟩ := by
        exact fun j => singularValuesSorted_antitone A (Nat.zero_le _)
      exact (by
      have h_max_le_ge : ∃ j, singularValues A i = singularValuesSorted A j := by
        have h_exists_j : singularValues A i ∈ Multiset.sort (Finset.univ.val.map (singularValues A)) (· ≥ ·) := by
          simp [Multiset.mem_sort]
        obtain ⟨j, hj⟩ := List.mem_iff_get.mp h_exists_j
        exact ⟨⟨j, by simpa using j.2⟩, hj.symm⟩
      aesop)
    exact Finset.sup'_le _ _ fun i _ => h_max_le_ge i
