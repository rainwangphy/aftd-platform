import AFTD.Prelude

/-!
# prime_ge_two_mul_add_one_of_odd_k

Topic: information   Node: 564d325c2a94

Provenance: helper lemma. arXiv:2610.28047 Corollary 3.2

If l is a prime number and k ≥ 2 is an odd natural number such that k divides l - 1, then l ≥ 2 * k + 1.
-/

/-- An odd divisor k ≥ 2 of l - 1 for a prime l satisfies l ≥ 2k + 1. -/
theorem prime_ge_two_mul_add_one_of_odd_k {l k : ℕ} (hl : Nat.Prime l) (hk_odd : Odd k)
    (hdiv : k ∣ l - 1) (hk_ge : 2 ≤ k) :
    2 * k + 1 ≤ l := by
  have hdiv' := hdiv
  obtain ⟨m, hm⟩ := hdiv
  have hl2 : l ≠ 2 := by
    intro h
    subst l
    have h1 : k ∣ 1 := by simpa using hdiv'
    have hk1 : k ≤ 1 := Nat.le_of_dvd (by norm_num) h1
    omega
  have hl_odd : Odd l := hl.odd_of_ne_two hl2
  have hEven : Even (l - 1) := Nat.Odd.sub_odd hl_odd odd_one
  have hm_even : Even m := by
    rw [hm] at hEven
    rcases Nat.even_mul.mp hEven with hk_even | hm_even
    · exact absurd hk_even (Nat.not_even_iff_odd.mpr hk_odd)
    · exact hm_even
  have hm_ne0 : m ≠ 0 := by
    intro hm0
    rw [hm0, Nat.mul_zero] at hm
    have hl2le := hl.two_le
    have hl1 : l = 1 := by omega
    exact hl.ne_one hl1
  have hm_ge : 2 ≤ m := by
    have h1 := Nat.one_lt_of_ne_zero_of_even hm_ne0 hm_even
    omega
  have hl_eq : l = k * m + 1 := by
    have hl1 := hl.one_lt
    omega
  have hkm : 2 * k ≤ k * m := by
    calc 2 * k = k * 2 := by ring
      _ ≤ k * m := Nat.mul_le_mul_left k hm_ge
  omega
