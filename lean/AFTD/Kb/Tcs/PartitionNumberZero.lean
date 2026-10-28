import AFTD.Prelude
import AFTD.Kb.Tcs.PartitionNumber
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# partition_number_zero

Topic: combinatorics   Node: 87c8062fa293

Provenance: helper lemma. arXiv:2610.01747 Section 6.1

The integer-valued partition function partition_number evaluated at 0 equals 1.
-/

/-- The partition function at 0 equals 1. -/
theorem partition_number_zero : partition_number 0 = 1 := by
  simp [partition_number]
