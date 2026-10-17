import AFTD.Prelude
import AFTD.Kb.Tcs.SingularValuesSorted
import AFTD.Kb.Tcs.SingularValues
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# singularValuesSorted_antitone

Topic: quantum   Node: 0c7f18f10f42

Provenance: formalization of a published result. Source: QuantumInfo, `singularValuesSorted_antitone`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Majorization.lean (Copyright (c) 2026 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Sorted singular values are antitone (decreasing).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {d : Type*} [Fintype d] [DecidableEq d] in
/-- Sorted singular values are antitone (decreasing). -/
lemma singularValuesSorted_antitone (A : Matrix d d ℂ) :
    Antitone (singularValuesSorted A) := by
  intro i j hij
  have h_sorted : List.Pairwise (· ≥ ·) (Finset.univ.val.map (singularValues A) |>.sort (· ≥ ·)) := by
    exact Multiset.pairwise_sort _ _
  exact h_sorted.rel_get_of_le hij
