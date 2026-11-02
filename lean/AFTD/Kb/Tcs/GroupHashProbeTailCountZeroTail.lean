import AFTD.Prelude
import AFTD.Kb.Tcs.GroupHashProbeTailCount
import AFTD.Kb.Tcs.GroupHashOccupiedSlots

/-!
# group_hash_probe_tail_count_zero_tail

Topic: data_structures   Node: 18f52040ce3b

Provenance: helper lemma. arXiv:2610.31363: A Sharp Analysis of Fixed Offset Hash Tables, serving OP-808

For any finite group G with decidable equality, table size n : ℕ, offset sequence r : Fin n → G, and insertion length t : ℕ, the probe tail count group_hash_probe_tail_count G n r t 0 is equal to (Fintype.card G) ^ (t + 1).
-/

/-- The probe tail count for threshold 0 equals the total number of insertion histories and query keys. -/
theorem group_hash_probe_tail_count_zero_tail (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    (n : ℕ) (r : Fin n → G) (t : ℕ) :
    group_hash_probe_tail_count G n r t 0 = (Fintype.card G) ^ (t + 1) := by
  unfold group_hash_probe_tail_count
  simp only [Nat.not_lt_zero, false_implies]
  rw [Finset.filter_true_of_mem]
  · rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fun]
    simp [pow_succ, mul_comm]
  · intro x _; simp
