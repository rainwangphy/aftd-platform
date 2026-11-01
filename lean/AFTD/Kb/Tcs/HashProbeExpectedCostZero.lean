import AFTD.Prelude
import AFTD.Kb.Tcs.HashProbeExpectedCost
import AFTD.Kb.Tcs.HashProbeTailProb
import AFTD.Kb.Tcs.HashOccupiedSlotsNil
import AFTD.Kb.Tcs.HashProbeTailCount
import AFTD.Kb.Tcs.HashOccupiedSlots

/-!
# hash_probe_expected_cost_zero

Topic: data_structures   Node: 7567589f3e4e

Provenance: helper lemma. scout/2610-31363-a-sharp-analysis-of-fixed-offset-hash-tables.md:333

For any table size n with [NeZero n] and any offset sequence r : Fin n → ZMod n, the expected probe cost hash_probe_expected_cost n r 0 into an empty table (t = 0) is 1.
-/

private lemma hash_probe_expected_cost_zero_tail_count_zero (n : ℕ) [NeZero n] (r : Fin n → ZMod n) :
    hash_probe_tail_count n r 0 0 = n := by
  unfold hash_probe_tail_count
  have hh : (Finset.univ.filter (fun (p : (Fin 0 → ZMod n) × ZMod n) =>
      ∀ j : Fin n, j.val < 0 → p.2 + r j ∈ hash_occupied_slots n r (List.ofFn p.1))) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro x hx j hj
    exact absurd hj (Nat.not_lt_zero _)
  rw [hh, Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  simp [ZMod.card]

private lemma hash_probe_expected_cost_zero_tail_count_succ (n : ℕ) [NeZero n] (r : Fin n → ZMod n) (k : ℕ) :
    hash_probe_tail_count n r 0 (k + 1) = 0 := by
  unfold hash_probe_tail_count
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p _ hh
  have h0 := hh (0 : Fin n) (by simp)
  rw [List.ofFn_zero, hash_occupied_slots_nil] at h0
  simpa using h0

private lemma hash_probe_expected_cost_zero_tail_prob_zero (n : ℕ) [NeZero n] (r : Fin n → ZMod n) :
    hash_probe_tail_prob n r 0 0 = 1 := by
  unfold hash_probe_tail_prob
  rw [hash_probe_expected_cost_zero_tail_count_zero]
  norm_num

private lemma hash_probe_expected_cost_zero_tail_prob_succ (n : ℕ) [NeZero n] (r : Fin n → ZMod n) (k : ℕ) :
    hash_probe_tail_prob n r 0 (k + 1) = 0 := by
  unfold hash_probe_tail_prob
  rw [hash_probe_expected_cost_zero_tail_count_succ]
  simp

/-- Inserting into an empty table always takes expected cost 1. -/
theorem hash_probe_expected_cost_zero (n : ℕ) [NeZero n] (r : Fin n → ZMod n) :
    hash_probe_expected_cost n r 0 = 1 := by
  unfold hash_probe_expected_cost
  have hsum : ∑ k ∈ Finset.range (n + 1), hash_probe_tail_prob n r 0 k
      = hash_probe_tail_prob n r 0 0 := by
    apply Finset.sum_eq_single 0
    · intro b _ hb0
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb0
      exact hash_probe_expected_cost_zero_tail_prob_succ n r k
    · intro h0
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h0
  rw [hsum, hash_probe_expected_cost_zero_tail_prob_zero]
