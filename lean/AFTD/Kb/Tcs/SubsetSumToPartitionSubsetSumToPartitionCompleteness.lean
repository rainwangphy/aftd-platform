import AFTD.Prelude
import AFTD.Kb.Tcs.SubsetSumToPartitionPartition
import AFTD.Kb.Tcs.SubsetSumToPartitionSubsetSum
import AFTD.Kb.Tcs.SubsetSumToPartitionPartitionWeight

/-!
# SubsetSumToPartition.SubsetSumToPartitionCompleteness

Topic: np_completeness   Node: 143e2cb2e970

Provenance: formalization of a published result. Source: Completeness of the Subset Sum to Partition reduction, as formalized in TCSlib (`SubsetSumToPartition.SubsetSumToPartitionCompleteness`). Lean proof by Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/SubsetSumToPartition.lean (Apache-2.0); 1 verbatim; compiled here.

Completeness of the Subset Sum to Partition reduction. Let $w : U \to \bbn$ be a weight function on a finite type $U$, and let $T \in \bbn$
satisfy $T \le \sum_{a} w(a)$. If the Subset Sum instance $(w, T)$ has a solution — some
subset of $U$ with total weight exactly $T$ — then the Partition instance on the
augmented type $U \oplus \mathrm{Bool}$ whose weights are given by the reduction weight
function built from $(w, T)$ has a solution; that is, $U \oplus \mathrm{Bool}$ admits a
subset whose total weight equals that of its complement.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {U : Type*} [Fintype U] [DecidableEq U] in
/-- Completeness of reduction from Subset Sum to Partition. Note the hypothesis `(h : T ≤ ∑ a, w a)`. Because Lean's natural numbers `ℕ` do not support negative numbers (subtraction truncates at 0), we must assert that the target `T` is not strictly greater than the total weight of all items. (If it were, the Subset Sum would be trivially false anyway). -/
theorem SubsetSumToPartition.SubsetSumToPartitionCompleteness (w : U → ℕ) (T : ℕ) (h : T ≤ ∑ a, w a):
  SubsetSum w T → Partition (partitionWeight w T) := by
  intro ⟨S, hS⟩
  -- Witness: {inl a | a ∈ S} ∪ {inr true}
  let S' := S.image Sum.inl ∪ {Sum.inr true}
  refine ⟨S', ?_⟩
  have hDisj : Disjoint (S.image Sum.inl) ({Sum.inr true} : Finset (U ⊕ Bool))
    := by simp
  -- Step 1: Left side sums to 2W
  have hSumLHS : ∑ b ∈ S', partitionWeight w T b = 2 * (∑ a, w a) := by
    show ∑ b ∈ S.image Sum.inl ∪ {Sum.inr true}, partitionWeight w T b = 2 * (∑ a, w a)
    rw [Finset.sum_union hDisj, Finset.sum_image (Sum.inl_injective.injOn),
      Finset.sum_singleton]
    simp only [partitionWeight]
    omega
  -- Step 2: Total sum is 4W
  have hTotalSum : ∑ b : U ⊕ Bool, partitionWeight w T b = 4 * (∑ a, w a) := by
    rw [Fintype.sum_sum_type, Fintype.sum_bool]
    simp only [partitionWeight]
    omega
  -- Step 3: Use complement to get right side = 2W
  have hadd := Finset.sum_add_sum_compl S' (partitionWeight w T)
  rw [hTotalSum] at hadd
  omega
