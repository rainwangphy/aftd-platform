import AFTD.Prelude

/-!
# mondrian_prime_power_dvd_sides

Topic: combinatorics   Node: b1ab490c6403

Provenance: helper lemma. Helper for OP-280 and mondrian_perfect_partition_large_prime_iff. Related work: arXiv:2610.19193, Section 1 (perfect partitions and scaling); arXiv:2007.09639, Theorem 4.1 (available shapes and prime-power exclusions).

If p is prime and exceeds c, positive x and y at most c times p to the e whose product is divisible by p to the 2e must each be divisible by p to the e.
-/

theorem mondrian_prime_power_dvd_sides (c p e x y : ℕ) (hp : Nat.Prime p)
    (hpc : c < p) (hx : 0 < x) (hy : 0 < y)
    (hxn : x ≤ c * p ^ e) (hyn : y ≤ c * p ^ e)
    (hxy : p ^ (2 * e) ∣ x * y) : p ^ e ∣ x ∧ p ^ e ∣ y := by
  obtain ⟨a, b, hax, hby, hab⟩ := exists_dvd_and_dvd_of_dvd_mul hxy
  have ha : a ∣ p ^ (2 * e) := by rw [hab]; exact dvd_mul_right a b
  have hb : b ∣ p ^ (2 * e) := by rw [hab]; exact dvd_mul_left b a
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).mp ha
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hp).mp hb
  have hij : 2 * e = i + j := by
    apply Nat.pow_right_injective hp.two_le
    simpa only [pow_add] using hab
  have hxe : p ^ i < p ^ (e + 1) := by
    calc
      p ^ i ≤ x := Nat.le_of_dvd hx hax
      _ ≤ c * p ^ e := hxn
      _ < p * p ^ e := Nat.mul_lt_mul_of_pos_right hpc (pow_pos hp.pos e)
      _ = p ^ (e + 1) := by rw [pow_succ, Nat.mul_comm]
  have hye : p ^ j < p ^ (e + 1) := by
    calc
      p ^ j ≤ y := Nat.le_of_dvd hy hby
      _ ≤ c * p ^ e := hyn
      _ < p * p ^ e := Nat.mul_lt_mul_of_pos_right hpc (pow_pos hp.pos e)
      _ = p ^ (e + 1) := by rw [pow_succ, Nat.mul_comm]
  have hi' := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hxe
  have hj' := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hye
  have hie : i = e := by omega
  have hje : j = e := by omega
  simpa [hie, hje] using And.intro hax hby
