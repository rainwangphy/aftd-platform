import AFTD.Prelude

/-!
# continuous_antipodal_circle_zero

Topic: quantum   Node: f41ea1581262

Provenance: helper lemma.

A continuous real function on the plane that has opposite values at the two horizontal antipodes has a zero on the unit circle.
-/

theorem continuous_antipodal_circle_zero (f : ℝ × ℝ → ℝ)
    (hf : Continuous f) (hodd : f (-1, 0) = -f (1, 0)) :
    ∃ x y : ℝ, x^2 + y^2 = 1 ∧ f (x, y) = 0 := by
  let g : ℝ → ℝ := fun t => f (Real.cos t, Real.sin t)
  have hg : Continuous g := by
    dsimp [g]
    exact hf.comp (Real.continuous_cos.prodMk Real.continuous_sin)
  have hpi : g Real.pi = -g 0 := by
    simpa [g] using hodd
  have hz : (0 : ℝ) ∈ g '' Set.Icc 0 Real.pi := by
    rcases le_total (g 0) 0 with h | h
    · apply intermediate_value_Icc Real.pi_nonneg hg.continuousOn
      exact ⟨h, by rw [hpi]; linarith⟩
    · apply intermediate_value_Icc' Real.pi_nonneg hg.continuousOn
      exact ⟨by rw [hpi]; linarith, h⟩
  obtain ⟨t, _, ht⟩ := hz
  refine ⟨Real.cos t, Real.sin t, ?_, ?_⟩
  · nlinarith [Real.sin_sq_add_cos_sq t]
  · exact ht
