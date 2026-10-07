import AFTD.Prelude
import AFTD.Kb.Tcs.K4CycleMatroid
import AFTD.Kb.Tcs.K4Forest
import AFTD.Kb.Tcs.K4ForestSubset
import AFTD.Kb.Tcs.K4ForestAug

/-!
# k4_cycle_matroid_indep

Topic: combinatorics   Node: f779a6c91fe0

Provenance: helper lemma. step towards matroid_common_list_colorable_two_not_of_colorable_two (arXiv:2610.07318 (A note on the list chromatic number of two matroids), Theorem 1.1)

A set of edges is independent in M(K₄) exactly when it is a forest.
-/

theorem k4_cycle_matroid_indep (S : Set (Fin 6)) [DecidablePred (· ∈ S)] :
    k4_cycle_matroid.Indep S ↔ k4_forest (Finset.univ.filter (· ∈ S)) := by
  have h := IndepMatroid.ofFinset_indep (α := Fin 6) Set.univ k4_forest (by decide)
    k4_forest_subset k4_forest_aug (fun _ _ => Set.subset_univ _)
    (I := Finset.univ.filter (· ∈ S))
  have hS : ((Finset.univ.filter (· ∈ S) : Finset (Fin 6)) : Set (Fin 6)) = S := by
    ext x; simp
  rw [hS] at h
  exact h
