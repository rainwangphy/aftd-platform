import AFTD.Prelude

/-!
# not_div_padicValNat_dvd_div_padicValNat

Topic: elementary_number_theory   Node: b66a70a2f75c

Provenance: original. Related work: refutes `div_padicValNat_dvd_div_padicValNat`

The statement `div_padicValNat_dvd_div_padicValNat` is false: The statement is false for non-prime p. Take d = 6, n = 48, p = 4. Then 0 < 6 and 6 ∣ 48. Since 4 ∤ 6, padicValNat 4 6 = 0, so d / 4^{padicValNat 4 6} = 6. Since 4^2 = 16 divides 48 but 4^3 = 64 does not, padicValNat 4 48 = 2, so n / 4^{padicValNat 4 48} = 48 / 16 = 3. But 6 does not divide 3. The statement is presumably intended with p prime (or with a hypothesis such as Fact p.Prime).
-/

theorem not_div_padicValNat_dvd_div_padicValNat : ¬ (∀ {d n p : ℕ} (hd : 0 < d) (hdn : d ∣ n), d / p ^ padicValNat p d ∣ n / p ^ padicValNat p n) := by
  intro h
  have h6 : padicValNat 4 6 = 0 := by
    rw [padicValNat.eq_zero_of_not_dvd]
    norm_num
  have h48 : padicValNat 4 48 = 2 := by
    have h : Nat.maxPowDvdDiv 4 48 = (2, 3) := by
      apply Nat.maxPowDvdDiv_of_pow_mul_eq (by norm_num : (48:ℕ) ≠ 0)
      · norm_num
      · norm_num
    simp [padicValNat, h]
  have hc : 6 / 4 ^ padicValNat 4 6 ∣ 48 / 4 ^ padicValNat 4 48 :=
    h (d := 6) (n := 48) (p := 4) (by norm_num) (by norm_num)
  rw [h6, h48] at hc
  norm_num at hc
