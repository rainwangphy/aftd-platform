import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeK4PartitionMatroid
import AFTD.Kb.Tcs.ThreeK4PartitionClass

/-!
# three_k4_partition_matroid_indep

Topic: combinatorics   Node: 12fdb8489107

Provenance: helper lemma. step towards matroid_common_list_colorable_two_not_of_colorable_two (arXiv:2610.07318 (A note on the list chromatic number of two matroids), Theorem 1.1)

A set is independent in the partition matroid M₂ exactly when the class map is injective on it.
-/

theorem three_k4_partition_matroid_indep (S : Set (Fin 3 × Fin 6)) :
    three_k4_partition_matroid.Indep S ↔ Set.InjOn three_k4_partition_class S := by
  simp [three_k4_partition_matroid]
