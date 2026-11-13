import AFTD.Prelude

/-!
# forest_carpool_fibonacci_growth

Topic: online_algorithms   Node: 526e4f67002f

Provenance: helper lemma. Helper for OP-1106, forest greedy carpooling; related background arXiv:2611.00388.

For every integer level D at least 2, its Fibonacci number is at least 2 to the power (D-2)/2.
-/

private lemma forest_fib_rpow_shifted (n : ℕ) :
    (2 : ℝ) ^ ((n : ℝ) / 2) ≤ (Nat.fib (n + 2) : ℝ) := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [Nat.fib]
  | one =>
    have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
      (show (1 : ℝ) / 2 ≤ 1 by norm_num)
    norm_num [Nat.fib, Real.rpow_one] at h ⊢ <;> exact h
  | more n ih0 ih1 =>
    have hn : 2 * Nat.fib (n + 2) ≤ Nat.fib (n + 4) := by
      have hm : Nat.fib (n + 2) ≤ Nat.fib (n + 3) := by
        simpa [Nat.add_assoc] using (Nat.fib_le_fib_succ (n := n + 2))
      have he : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := by
        simpa [Nat.add_assoc] using (Nat.fib_add_two (n := n + 2))
      omega
    have hr : (2 : ℝ) * (Nat.fib (n + 2) : ℝ) ≤ (Nat.fib (n + 4) : ℝ) := by exact_mod_cast hn
    have he : (((n + 2 : ℕ) : ℝ) / 2) = (n : ℝ) / 2 + 1 := by push_cast; ring
    have hexp : (2 : ℝ) ^ (((n + 2 : ℕ) : ℝ) / 2) = 2 * (2 : ℝ) ^ ((n : ℝ) / 2) := by
      rw [he, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
      ring
    calc
      _ = 2 * (2 : ℝ) ^ ((n : ℝ) / 2) := hexp
      _ ≤ 2 * (Nat.fib (n + 2) : ℝ) := by nlinarith
      _ ≤ _ := by simpa [Nat.add_assoc] using hr

theorem forest_carpool_fibonacci_growth (D : ℕ) (hD : 2 ≤ D) :
  (2 : ℝ) ^ (((D : ℝ) - 2) / 2) ≤ (Nat.fib D : ℝ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hD
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using forest_fib_rpow_shifted n
