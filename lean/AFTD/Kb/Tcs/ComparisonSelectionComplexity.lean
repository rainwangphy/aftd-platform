import AFTD.Prelude
import AFTD.Kb.Tcs.ComparisonTreeSelectsRank
import AFTD.Kb.Tcs.ComparisonTreeDepth
import AFTD.Kb.Tcs.ComparisonTree

/-!
# comparison_selection_complexity

Topic: algorithms   Node: 23a11c4904d2

Provenance: formalization of a published result. Source: scout/2610-18740-selecting-the-7th-smallest-of-16-elements-takes-exactly-28.md:Sec. 3

The worst-case comparison complexity to select the element of rank r : Fin n among n elements, defined as the infimum of the depths of all comparison decision trees T : ComparisonTree n that satisfy comparison_tree_selects_rank T r.
-/

/-- Worst-case comparison complexity to select the element of 0-based rank r in Fin n. -/
noncomputable def comparison_selection_complexity {n : ℕ} (r : Fin n) : ℕ := sInf { d : ℕ | ∃ T : ComparisonTree n, comparison_tree_selects_rank T r ∧ comparison_tree_depth T = d }
