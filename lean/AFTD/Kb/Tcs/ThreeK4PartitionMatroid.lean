import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeK4PartitionClass

/-!
# three_k4_partition_matroid

Topic: combinatorics   Node: b57010b74864

Provenance: formalization of a published result. Source: arXiv:2610.07318 (A note on the list chromatic number of two matroids), proof of Theorem 1.1 (M₂)

The unit-capacity partition matroid M₂ whose independent sets meet every class of three_k4_partition_class at most once.
-/

/-- The unit-capacity partition matroid M₂ whose independent sets meet every class of three_k4_partition_class at most once. -/
def three_k4_partition_matroid : Matroid (Fin 3 × Fin 6) :=
  (Matroid.freeOn (Set.univ : Set (Fin 9))).comap three_k4_partition_class
