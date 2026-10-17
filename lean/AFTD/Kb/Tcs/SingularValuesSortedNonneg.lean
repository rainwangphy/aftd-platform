import AFTD.Prelude
import AFTD.Kb.Tcs.SingularValuesSorted
import AFTD.Kb.Tcs.SingularValues
import AFTD.Kb.Tcs.SingularValuesNonneg

/-!
# singularValuesSorted_nonneg

Topic: quantum   Node: 705c0e53c5ab

Provenance: formalization of a published result. Source: QuantumInfo, `singularValuesSorted_nonneg`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Majorization.lean (Copyright (c) 2026 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Sorted singular values are nonneg.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {d : Type*} [Fintype d] [DecidableEq d] in
/-- Sorted singular values are nonneg. -/
lemma singularValuesSorted_nonneg (A : Matrix d d ℂ) (i : Fin (Fintype.card d)) :
    0 ≤ singularValuesSorted A i := by
  have h_nonneg : ∀ i, 0 ≤ (singularValues A i) := by
    exact singularValues_nonneg A
  have h_sorted_nonneg : ∀ {l : List ℝ}, (∀ x ∈ l, 0 ≤ x) → ∀ i < l.length, 0 ≤ l[i]! := by
    aesop
  contrapose! h_sorted_nonneg
  use Multiset.sort (Finset.univ.val.map (singularValues A)) (· ≥ ·)
  refine' ⟨_, i, _, _⟩
  · aesop
  · simp [Finset.card_univ]
  · convert h_sorted_nonneg using 1
    unfold singularValuesSorted; aesop
