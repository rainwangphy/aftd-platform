import AFTD.Prelude
import AFTD.Kb.Tcs.ComparisonTreeSelectsRank
import AFTD.Kb.Tcs.ComparisonTree
import AFTD.Kb.Tcs.ComparisonTreeEval

/-!
# comparison_tree_selects_rank_one_zero

Topic: algorithms   Node: fd6717731a9c

Provenance: helper lemma. scout/2610-18740-selecting-the-7th-smallest-of-16-elements-takes-exactly-28.md:Sec. 3

For n = 1, the single leaf comparison decision tree returning index 0 correctly selects rank 0.
-/

/-- The leaf comparison tree on 1 element selects rank 0. -/
theorem comparison_tree_selects_rank_one_zero :
    comparison_tree_selects_rank (ComparisonTree.leaf (0 : Fin 1)) (0 : Fin 1) := by
  intro σ
  exact Subsingleton.elim _ _
