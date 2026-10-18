import AFTD.Prelude
import AFTD.Kb.Tcs.ComparisonTreeSelectsRank
import AFTD.Kb.Tcs.ComparisonTree
import AFTD.Kb.Tcs.ComparisonTreeEval

/-!
# not_comparison_tree_selects_rank_two_leaf_one

Topic: algorithms   Node: f28f090f9161

Provenance: helper lemma. scout/2610-18740-selecting-the-7th-smallest-of-16-elements-takes-exactly-28.md:Sec. 3

For n = 2, the leaf comparison decision tree returning index 0 does not correctly select rank 1.
-/

/-- The leaf comparison tree returning 0 on 2 elements does not select rank 1. -/
theorem not_comparison_tree_selects_rank_two_leaf_one :
    ¬ comparison_tree_selects_rank (ComparisonTree.leaf (0 : Fin 2)) (1 : Fin 2) := by
  intro h
  have h0 := h (Equiv.refl (Fin 2))
  simp [comparison_tree_eval] at h0
