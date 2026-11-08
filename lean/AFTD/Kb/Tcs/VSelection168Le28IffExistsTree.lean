import AFTD.Prelude
import AFTD.Kb.Tcs.VSelectionLeIff
import AFTD.Kb.Tcs.VSelection
import AFTD.Kb.Tcs.ComparisonTreeSelectsRank
import AFTD.Kb.Tcs.ComparisonTreeDepth
import AFTD.Kb.Tcs.ComparisonTree

/-!
# v_selection_16_8_le_28_iff_exists_tree

Topic: algorithms   Node: 9aa81c116a9d

Provenance: helper lemma. arXiv:2610.18740 Sec. 2, Selecting the 7th Smallest of 16 Elements Takes Exactly 28 Comparisons

The worst-case comparison complexity of selecting the 8th smallest element among 16 elements is at most 28 (that is, V_8(16) ≤ 28) if and only if there exists a comparison decision tree on 16 elements of depth at most 28 that correctly selects rank 7.
-/

/-- V_8(16) ≤ 28 if and only if there exists a correct comparison decision tree of depth ≤ 28 for rank 7 on 16 elements. -/
theorem v_selection_16_8_le_28_iff_exists_tree :
    v_selection 16 8 ≤ 28 ↔ ∃ T : ComparisonTree 16, comparison_tree_selects_rank T (7 : Fin 16) ∧ comparison_tree_depth T ≤ 28 := v_selection_le_iff 16 8 28 (by omega) (by omega)
