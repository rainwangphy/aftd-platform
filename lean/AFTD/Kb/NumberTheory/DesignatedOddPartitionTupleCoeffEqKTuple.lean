import AFTD.Prelude
import AFTD.Kb.NumberTheory.DesignatedOddPartGenFun
import AFTD.Kb.NumberTheory.DesignatedOddPartitionGenFun
import AFTD.Kb.NumberTheory.DesignatedOddPartitionTupleCoeff
import AFTD.Kb.NumberTheory.DesignatedOddPartitionKTuple
import AFTD.Kb.NumberTheory.DesignatedOddPartitionWeight
import AFTD.Kb.NumberTheory.DesignatedOddPartitionCharacter

/-!
# designated_odd_partition_tuple_coeff_eq_k_tuple

Topic: elementary_number_theory   Node: f421207aa616

Provenance: helper lemma. step towards designated_odd_partition_tuple_thm_4_6

The two definitions of B_k(n) in this topic, designated_odd_partition_tuple_coeff and designated_odd_partition_k_tuple, are the same function: both are the nth coefficient of the kth power of the generating function of partitions into odd parts with designated summands.
-/

/-- The coefficient function defined from designated_odd_part_gen_fun equals the one defined from designated_odd_partition_gen_fun; the two weight functions agree. -/
theorem designated_odd_partition_tuple_coeff_eq_k_tuple : designated_odd_partition_tuple_coeff = designated_odd_partition_k_tuple := by
  have hchar : designated_odd_partition_character = designated_odd_partition_weight := by
    funext i c
    simp only [designated_odd_partition_character, designated_odd_partition_weight]
    by_cases h : Odd i
    · simp [h, Nat.odd_iff.mp h]
    · have h2 : i % 2 ≠ 1 := fun hh => h (Nat.odd_iff.mpr hh)
      simp [h, h2]
  unfold designated_odd_partition_tuple_coeff designated_odd_partition_k_tuple
    designated_odd_part_gen_fun designated_odd_partition_gen_fun
  rw [← hchar]
