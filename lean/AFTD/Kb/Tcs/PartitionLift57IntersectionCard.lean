import AFTD.Prelude
import AFTD.Kb.Tcs.PartitionLift57

/-!
# partition_lift_57_intersection_card

Topic: combinatorics   Node: e392cb7fdcfb

Provenance: helper lemma. arXiv:2610.01747, Eq. (25)

For t ≥ 1, the multiset intersection size of two lifted partitions exceeds the multiset intersection size of the original partitions of 57 by exactly t - 1.
-/

/-- Common parts count of two lifted partitions increases by exactly t - 1. -/
theorem partition_lift_57_intersection_card (t : ℕ) (ht : 1 ≤ t)
    (p q : Nat.Partition 57) :
    ((partition_lift_57 t ht p).parts ∩ (partition_lift_57 t ht q).parts).card =
      (p.parts ∩ q.parts).card + (t - 1) := by
  simp only [partition_lift_57]
  rw [← Multiset.inter_add_distrib, Multiset.card_add, Multiset.card_replicate]
