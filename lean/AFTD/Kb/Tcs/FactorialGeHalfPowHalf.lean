import AFTD.Prelude

/-!
# factorial_ge_half_pow_half

Topic: algorithms   Node: ab3660c95d3c

For every natural number n, (n/2)^{⌊n/2⌋} ≤ n!, where the base n/2 is the real number n/2 and the exponent ⌊n/2⌋ is the natural number n/2. Equivalently n! ≥ (n/2)^{n/2}.
-/

theorem factorial_ge_half_pow_half (n : ℕ) :
    ((n : ℝ) / 2) ^ (n / 2) ≤ (n.factorial : ℝ) := by
  set m := n / 2 with hm
  have hmle : m ≤ n := Nat.div_le_self n 2
  have hbase : (n + 1 - m) ^ m ≤ n.factorial := by
    have h1 : (n + 1 - m) ^ m ≤ n.descFactorial m := Nat.pow_sub_le_descFactorial n m
    have h2 : (n - m).factorial * n.descFactorial m = n.factorial :=
      Nat.factorial_mul_descFactorial hmle
    have h3 : n.descFactorial m ≤ (n - m).factorial * n.descFactorial m :=
      Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)
    rw [h2] at h3
    exact le_trans h1 h3
  have hcast : ((n : ℝ) / 2) ≤ ((n + 1 - m : ℕ) : ℝ) := by
    have h : n ≤ 2 * (n + 1 - m) := by omega
    have h' : (n : ℝ) ≤ 2 * ((n + 1 - m : ℕ) : ℝ) := by exact_mod_cast h
    linarith
  calc ((n : ℝ) / 2) ^ (n / 2) = ((n : ℝ) / 2) ^ m := by rw [hm]
    _ ≤ ((n + 1 - m : ℕ) : ℝ) ^ m := pow_le_pow_left₀ (by positivity) hcast m
    _ = ((n + 1 - m) ^ m : ℕ) := by rw [Nat.cast_pow]
    _ ≤ (n.factorial : ℝ) := by exact_mod_cast hbase
