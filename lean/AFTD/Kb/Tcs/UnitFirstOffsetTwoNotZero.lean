import AFTD.Prelude

/-!
# unit_first_offset_two_not_zero

Topic: data_structures   Node: 77a1c047c3ed

Provenance: helper lemma. step towards unit_first_fixed_offset_mean_probe_maximum

In ZMod n with n > 2, doubling any unit u yields a nonzero element u + u ≠ 0.
-/

/-- In ZMod n with n > 2, doubling any unit yields a nonzero element. -/
theorem unit_first_offset_two_not_zero (n : ℕ) [NeZero n] (hn : 2 < n)
    (u : ZMod n) (hu : IsUnit u) : u + u ≠ 0 := by
  intro h
  have h2 : (2 : ZMod n) * u = 0 := by
    calc (2 : ZMod n) * u = u + u := by ring
    _ = 0 := h
  have h3 : (2 : ZMod n) = 0 := (IsUnit.mul_left_eq_zero hu).mp h2
  have hdvd : n ∣ 2 := (CharP.cast_eq_zero_iff (ZMod n) n 2).mp h3
  have hle : n ≤ 2 := Nat.le_of_dvd (by decide) hdvd
  omega
