import AFTD.Prelude
import AFTD.Kb.NumberTheory.HalvingPartitionCountTwoMul
import AFTD.Kb.NumberTheory.HalvingPartitionCount
import AFTD.Kb.NumberTheory.IsHalvingPartition

/-!
# halving_partition_count_two_pow

Topic: elementary_number_theory   Node: 5d295d3a71a3

Provenance: formalization of a published result. Source: arXiv:2611.01243 Lemma 2

For every natural number e, the number of halving partitions of 2^e is equal to 1, that is, halving_partition_count (2 ^ e) = 1.
-/

theorem halving_partition_count_two_pow_aux_one : halving_partition_count 1 = 1 := by
  have hset : {p : List ℕ | is_halving_partition 1 p} = {[1]} := by
    ext p
    constructor
    · intro hp
      simp only [Set.mem_ofPred_eq, is_halving_partition] at hp
      obtain ⟨hpos, hsum, hcase⟩ := hp
      have hne : p ≠ [] := by
        intro h
        rw [h] at hsum
        simp at hsum
      have hlen : p.length ≤ 1 := by
        have h1 : ∀ i ∈ p, 1 ≤ i := fun i hi => hpos i hi
        have := List.length_le_sum_of_one_le p h1
        omega
      have hlen1 : p.length = 1 := by
        have : 0 < p.length := List.length_pos_iff.mpr hne
        omega
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hlen1
      simp only [List.sum_singleton] at hsum
      rw [hsum]
      rfl
    · intro hp
      simp only [Set.mem_singleton_iff] at hp
      rw [hp]
      simp [is_halving_partition]
  change ({p : List ℕ | is_halving_partition 1 p}).ncard = 1
  rw [hset, Set.ncard_singleton]

/-- For every natural number e, the number of halving partitions of 2^e is equal to 1. -/
theorem halving_partition_count_two_pow (e : ℕ) :
    halving_partition_count (2 ^ e) = 1 := by
  induction e with
  | zero => exact halving_partition_count_two_pow_aux_one
  | succ e ih =>
      rw [pow_succ]
      rw [mul_comm]
      rw [halving_partition_count_two_mul]
      exact ih
