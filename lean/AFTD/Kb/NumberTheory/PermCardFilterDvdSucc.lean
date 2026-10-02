import AFTD.Prelude

/-!
# perm_card_filter_dvd_succ

Topic: elementary_number_theory   Node: c6c592f87e56

For any permutation s of {0, ..., k-1} and any m, exactly floor(k/m) positions j have m dividing s(j) + 1 (the values s(j) + 1 run over 1, ..., k).
-/

theorem perm_card_filter_dvd_succ {k : ℕ} (σ : Equiv.Perm (Fin k)) (m : ℕ) :
    (Finset.univ.filter fun j : Fin k => m ∣ (σ j : ℕ) + 1).card = k / m := by
  have h1 : (Finset.univ.filter fun j : Fin k => m ∣ (σ j : ℕ) + 1).card =
      (Finset.univ.filter fun v : Fin k => m ∣ (v : ℕ) + 1).card := by
    rw [Finset.card_filter, Finset.card_filter]
    exact Equiv.sum_comp σ (fun v : Fin k => if m ∣ (v : ℕ) + 1 then 1 else 0)
  rw [h1, ← Nat.card_multiples k m, Finset.card_filter, Finset.card_filter,
    Fin.sum_univ_eq_sum_range (fun j => if m ∣ j + 1 then 1 else 0)]
