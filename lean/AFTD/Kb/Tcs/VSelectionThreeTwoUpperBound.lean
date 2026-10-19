import AFTD.Prelude
import AFTD.Kb.Tcs.VSelection
import AFTD.Kb.Tcs.ComparisonSelectionComplexity
import AFTD.Kb.Tcs.ComparisonTreeDepth
import AFTD.Kb.Tcs.ComparisonTreeSelectsRank
import AFTD.Kb.Tcs.ComparisonTreeEval
import AFTD.Kb.Tcs.ComparisonTree

/-!
# v_selection_three_two_upper_bound

Topic: algorithms   Node: 0510f97a8f3d

Provenance: helper lemma. step towards v_selection_16_8_upper_bound

The 2nd smallest (the median) of 3 distinct elements can be found using at most 3 pairwise comparisons, that is, V_2(3) ≤ 3.
-/

/-- Median of three in three comparisons: a nontrivial positive witness that `v_selection` is attained, complementing the n = 1 leaf and the negative n = 2 example already in the graph. -/
theorem v_selection_three_two_upper_bound : v_selection 3 2 ≤ 3 := by
  let T : ComparisonTree 3 :=
    .branch 0 1
      (.branch 1 2 (.leaf 1) (.branch 0 2 (.leaf 2) (.leaf 0)))
      (.branch 0 2 (.leaf 0) (.branch 1 2 (.leaf 2) (.leaf 1)))
  have hd : comparison_tree_depth T ≤ 3 := by decide
  have hT : comparison_tree_selects_rank T (⟨1, by norm_num⟩ : Fin 3) := by
    unfold comparison_tree_selects_rank
    decide
  unfold v_selection
  rw [dif_pos (show 0 < 2 ∧ 2 ≤ 3 by norm_num)]
  unfold comparison_selection_complexity
  exact le_trans (Nat.sInf_le ⟨T, hT, rfl⟩) hd
