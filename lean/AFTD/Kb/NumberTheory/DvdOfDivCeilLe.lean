import AFTD.Prelude

/-!
# dvd_of_div_ceil_le

Topic: elementary_number_theory   Node: 4c6544c1a82c

For m > 0, if ceil(k/m) <= floor(k/m) then m divides k.
-/

theorem dvd_of_div_ceil_le (m k : ℕ) (hm : 0 < m) (h : (k + m - 1) / m ≤ k / m) : m ∣ k := by
  by_contra hd
  have h1 : k / m * m ≤ k := Nat.div_mul_le_self k m
  have h2 : k / m * m ≠ k := fun e => hd ⟨k / m, by rw [mul_comm]; exact e.symm⟩
  have h3 : k / m + 1 ≤ (k + m - 1) / m := by
    rw [Nat.le_div_iff_mul_le hm, add_mul, one_mul]
    generalize k / m * m = x at h1 h2
    omega
  omega
