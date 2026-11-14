import AFTD.Prelude

/-!
# unit_complex_three_phase_surjective

Topic: quantum   Node: 1265b33aeadd

Provenance: helper lemma.

Every prescribed triple of unit complex phases can be realized by the three transverse phase combinations ++−, +−+, and −++.
-/

theorem unit_complex_three_phase_surjective (a b c : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    ∃ u v w : ℂ, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ ‖w‖ = 1 ∧
      u * v * star w = a ∧ u * star v * w = b ∧ star u * v * w = c := by
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (a*b) (n := 2) (by norm_num)
  obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq (a*c) (n := 2) (by norm_num)
  have hnu : ‖u‖ = 1 := by
    have h := congrArg norm hu
    rw [norm_pow, norm_mul, ha, hb] at h
    nlinarith [norm_nonneg u]
  have hnv : ‖v‖ = 1 := by
    have h := congrArg norm hv
    rw [norm_pow, norm_mul, ha, hc] at h
    nlinarith [norm_nonneg v]
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hu0 : u ≠ 0 := by intro h; simp [h] at hnu
  have hv0 : v ≠ 0 := by intro h; simp [h] at hnv
  let w : ℂ := u*v/a
  have hnw : ‖w‖ = 1 := by simp [w, norm_div, norm_mul, hnu, hnv, ha]
  have hsu : star u = u⁻¹ := by
    exact (Complex.inv_eq_conj hnu).symm
  have hsv : star v = v⁻¹ := by
    exact (Complex.inv_eq_conj hnv).symm
  have hsw : star w = w⁻¹ := by
    exact (Complex.inv_eq_conj hnw).symm
  refine ⟨u, v, w, hnu, hnv, hnw, ?_, ?_, ?_⟩
  · rw [hsw]
    dsimp [w]
    field_simp [ha0, hu0, hv0]
  · rw [hsv]
    dsimp [w]
    field_simp [ha0, hu0, hv0]
    linear_combination hu
  · rw [hsu]
    dsimp [w]
    field_simp [ha0, hu0, hv0]
    linear_combination hv
