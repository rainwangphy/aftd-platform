import AFTD.Prelude
import AFTD.Kb.Tcs.PartitionLift57

/-!
# partition_lift_57_injective

Topic: combinatorics   Node: 5241fe19aeed

Provenance: helper lemma. arXiv:2610.01747, Corollary 6.2 proof

For t ≥ 1, the lifting map that adds t - 1 ones to a partition of 57 is injective.
-/

/-- The lifting map on partitions adding t - 1 ones is injective. -/
theorem partition_lift_57_injective (t : ℕ) (ht : 1 ≤ t) :
    Function.Injective (partition_lift_57 t ht) := by
  intro p1 p2 h
  apply Nat.Partition.ext
  have hparts := congr_arg Nat.Partition.parts h
  dsimp [partition_lift_57] at hparts
  exact add_right_cancel hparts
