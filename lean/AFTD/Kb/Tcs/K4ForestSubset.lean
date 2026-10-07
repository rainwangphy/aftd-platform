import AFTD.Prelude
import AFTD.Kb.Tcs.K4Forest

/-!
# k4_forest_subset

Topic: combinatorics   Node: 6287e67286e4

Provenance: helper lemma. step towards matroid_common_list_colorable_two_not_of_colorable_two (arXiv:2610.07318 (A note on the list chromatic number of two matroids), Theorem 1.1)

Subsets of forests of K₄ are forests.
-/

set_option maxRecDepth 100000 in
theorem k4_forest_subset : ∀ ⦃I J : Finset (Fin 6)⦄, k4_forest J → I ⊆ J → k4_forest I := by
  decide +kernel
