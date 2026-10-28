import AFTD.Prelude
import AFTD.Kb.Tcs.PartitionNumber

/-!
# partition_number_neg

Topic: combinatorics   Node: 4075e837a98e

Provenance: helper lemma. arXiv:2610.01747 Section 6.1

For any integer m such that m < 0, the integer-valued partition function partition_number m equals 0.
-/

/-- The partition function at negative integers equals 0. -/
theorem partition_number_neg (m : ℤ) (hm : m < 0) : partition_number m = 0 := by
  simp [partition_number, not_le.mpr hm]
