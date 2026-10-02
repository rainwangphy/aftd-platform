import AFTD.Prelude

/-!
# range_card_filter_dvd

Topic: elementary_number_theory   Node: 68766d836d05

For m > 0, the numbers 0, ..., k-1 include exactly ceil(k/m) = (k + m - 1)/m multiples of m.
-/

theorem range_card_filter_dvd (m k : ℕ) (hm : 0 < m) :
    ((Finset.range k).filter (fun j => m ∣ j)).card = (k + m - 1) / m := by
  induction k with
  | zero => simp; exact (Nat.div_eq_of_lt (by omega)).symm
  | succ k ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    have e : k + 1 + m - 1 = (k + m - 1) + 1 := by omega
    rw [e, Nat.succ_div, ← ih]
    have e2 : k + m - 1 + 1 = k + m := by omega
    rw [e2]
    by_cases h : m ∣ k
    · have h' : m ∣ k + m := (Nat.dvd_add_self_right).2 h
      rw [if_pos h, if_pos h', Finset.card_insert_of_notMem (by simp)]
    · have h' : ¬ m ∣ k + m := fun h' => h ((Nat.dvd_add_self_right).1 h')
      rw [if_neg h, if_neg h']
      simp
