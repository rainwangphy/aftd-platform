import AFTD.Prelude
import AFTD.Kb.Tcs.K4Forest
import AFTD.Kb.Tcs.K4ForestAug
import AFTD.Kb.Tcs.K4ForestSubset

/-!
# k4_cycle_matroid

Topic: combinatorics   Node: 5c2dbc333ac2

Provenance: formalization of a published result. Source: arXiv:2610.07318 (A note on the list chromatic number of two matroids), proof of Theorem 1.1

The cycle matroid M(K₄) on the six edges of K₄.
-/

/-- The cycle matroid M(K₄) on the six edges of K₄. -/
def k4_cycle_matroid : Matroid (Fin 6) :=
  (IndepMatroid.ofFinset Set.univ k4_forest (by decide) k4_forest_subset k4_forest_aug
    (fun _ _ => Set.subset_univ _)).matroid
