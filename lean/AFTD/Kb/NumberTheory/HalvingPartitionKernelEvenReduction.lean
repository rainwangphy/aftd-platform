import AFTD.Prelude
import AFTD.Kb.NumberTheory.HalvingPartitionCountTwoMul
import AFTD.Kb.NumberTheory.HalvingPartitionCount

/-!
# halving_partition_kernel_even_reduction

Topic: elementary_number_theory   Node: 54940fde9e01

Provenance: helper lemma. arXiv:2611.01243 Sec. 6, paragraph 2

For all natural numbers e, r, and n, the halving partition count satisfies halving_partition_count (2 ^ (e + 1) * n + 2 * r) = halving_partition_count (2 ^ e * n + r).
-/

/-- Even-remainder elements of the 2-kernel reduce to elements at the preceding scale. -/
theorem halving_partition_kernel_even_reduction (e r n : ℕ) :
    halving_partition_count (2 ^ (e + 1) * n + 2 * r) = halving_partition_count (2 ^ e * n + r) := by
  rw [show 2 ^ (e + 1) * n + 2 * r = 2 * (2 ^ e * n + r) by ring]
  exact halving_partition_count_two_mul _
