import AFTD.Prelude
import AFTD.Kb.Tcs.GroupHashProbeTailCount
import AFTD.Kb.Tcs.GroupHashOccupiedSlots
import AFTD.Kb.Tcs.GroupHashInsertStep

/-!
# group_hash_probe_tail_count_t_zero_succ

Topic: data_structures   Node: 3f04c369bc45

Provenance: helper lemma. arXiv:2610.31363: A Sharp Analysis of Fixed Offset Hash Tables, serving OP-808

For any finite group G with decidable equality, table size n : ℕ with 0 < n, offset sequence r : Fin n → G, and natural number c, the probe tail count when inserting into an empty table group_hash_probe_tail_count G n r 0 (c + 1) is equal to 0.
-/

/-- The probe tail count for positive threshold when inserting into an empty table is 0. -/
theorem group_hash_probe_tail_count_t_zero_succ (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    (n : ℕ) (r : Fin n → G) (c : ℕ) (hn : 0 < n) :
    group_hash_probe_tail_count G n r 0 (c + 1) = 0 := by
  unfold group_hash_probe_tail_count
  simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx h
  have hmem := h ⟨0, hn⟩ (Nat.succ_pos c)
  simp [group_hash_occupied_slots] at hmem
