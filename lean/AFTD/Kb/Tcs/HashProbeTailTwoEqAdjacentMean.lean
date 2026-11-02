import AFTD.Prelude
import AFTD.Kb.Tcs.HashAdjacentCount
import AFTD.Kb.Tcs.HashProbeTailProb
import AFTD.Kb.Tcs.HashProbeTailCount
import AFTD.Kb.Tcs.HashOccupiedSlots
import AFTD.Kb.Tcs.Order

/-!
# hash_probe_tail_two_eq_adjacent_mean

Topic: data_structures   Node: c69b9f379612

Provenance: helper lemma. Unit-first fixed-offset mean-probe extremality; experiments 11670–11680 and arXiv:2610.31363.

The second probe-cost tail equals the expected number of occupied adjacent pairs, divided by the table size.
-/

open Finset

private lemma hash_probe_tail_two_eq_adjacent_mean_filter_finset
    (n : ℕ) [NeZero n] (hn : 2 ≤ n) (r : Fin n → ZMod n) (hr0 : r 0 = 0)
    (T : Finset (ZMod n)) :
    univ.filter (fun x : ZMod n => ∀ j : Fin n, j.val < 2 → x + r j ∈ T) =
      {x ∈ T | x + r 1 ∈ T} := by
  ext x
  simp only [mem_filter, mem_univ, true_and, Order.lt_two_iff]
  have h1_val : (1 : Fin n).val = 1 := by
    rw [Fin.val_one']
    exact Nat.mod_eq_of_lt (by omega)
  have h0_val : (0 : Fin n).val = 0 := Fin.val_zero n
  constructor
  · intro h
    have h0 : x ∈ T := by
      have hj : (0 : Fin n).val ≤ 1 := by rw [h0_val]; decide
      have h' := h 0 hj
      rwa [hr0, add_zero] at h'
    have h1 : x + r 1 ∈ T := by
      have hj : (1 : Fin n).val ≤ 1 := by rw [h1_val]
      exact h 1 hj
    exact ⟨h0, h1⟩
  · intro ⟨h0, h1⟩ j hj
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with hj0 | hj1
    · have : j = 0 := by ext; rw [hj0, h0_val]
      rw [this, hr0, add_zero]
      exact h0
    · have : j = 1 := by ext; rw [hj1, h1_val]
      rw [this]
      exact h1

private lemma hash_probe_tail_two_eq_adjacent_mean_tail_count_eq
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (r : Fin n → ZMod n) (hr0 : r 0 = 0) (t : ℕ) :
    hash_probe_tail_count n r t 2 =
      ∑ A : Fin t → ZMod n, hash_adjacent_count n (r 1) (hash_occupied_slots n r (List.ofFn A)) := by
  unfold hash_probe_tail_count
  simp_rw [card_filter, Fintype.sum_prod_type]
  congr 1 with A
  rw [← card_filter]
  unfold hash_adjacent_count
  rw [hash_probe_tail_two_eq_adjacent_mean_filter_finset n hn r hr0]

theorem hash_probe_tail_two_eq_adjacent_mean (n : ℕ) [NeZero n] (hn : 2 ≤ n)
  (r : Fin n → ZMod n) (hr0 : r 0 = 0) (t : ℕ) :
  (n : ℝ) * hash_probe_tail_prob n r t 2 =
    (∑ A : Fin t → ZMod n,
      (hash_adjacent_count n (r 1) (hash_occupied_slots n r (List.ofFn A)) : ℝ)) / (n : ℝ)^t := by
  unfold hash_probe_tail_prob
  rw [hash_probe_tail_two_eq_adjacent_mean_tail_count_eq n hn r hr0 t]
  push_cast
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hpow : (n : ℝ) ^ (t + 1) = (n : ℝ) ^ t * (n : ℝ) := by rw [pow_succ]
  rw [hpow]
  rw [div_mul_eq_div_div, mul_div_cancel₀ _ hn_ne]
