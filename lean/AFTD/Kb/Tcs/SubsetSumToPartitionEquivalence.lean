import AFTD.Prelude
import AFTD.Kb.Tcs.SubsetSumToPartitionSubsetSumToPartitionCompleteness
import AFTD.Kb.Tcs.SubsetSumToPartitionSubsetSumToPartitionSoundness
import AFTD.Kb.Tcs.SubsetSumToPartitionPartitionWeight
import AFTD.Kb.Tcs.SubsetSumToPartitionSubsetSum
import AFTD.Kb.Tcs.SubsetSumToPartitionPartition

/-!
# subset_sum_to_partition_equivalence

Topic: np_completeness   Node: 61316dc3ffcf

Provenance: formalization of a published result. Source: Karp (1972), 'Reducibility among Combinatorial Problems'; Garey & Johnson (1979)

Let w : U → ℕ be a weight function on a finite type U, and let T : ℕ satisfy T ≤ ∑ a, w a. Then the Subset Sum instance (w, T) has a solution if and only if the augmented Partition instance with weight function SubsetSumToPartition.partitionWeight w T has a solution.
-/

/-- Correctness of the Subset Sum to Partition reduction under the target bound T ≤ ∑ a, w a. -/
theorem subset_sum_to_partition_equivalence {U : Type*} [Fintype U] [DecidableEq U]
    (w : U → ℕ) (T : ℕ) (h : T ≤ ∑ a, w a) :
    SubsetSumToPartition.SubsetSum w T ↔
      SubsetSumToPartition.Partition (SubsetSumToPartition.partitionWeight w T) := ⟨SubsetSumToPartition.SubsetSumToPartitionCompleteness w T h,
   SubsetSumToPartition.SubsetSumToPartitionSoundness w T h⟩
