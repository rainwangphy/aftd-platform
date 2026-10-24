import AFTD.Prelude

/-!
# planar_necklace_continuous_odd_exists_zero

Topic: fair_division   Node: 2f7786817fd9

Provenance: helper lemma. step towards planar_necklace_three_agents_three_cuts

A continuous function f : ℝ → ℝ that is odd with respect to π, in the sense that f (x + π) = - f x for all x, has a zero.
-/

/-- A continuous function vanishing to order π up to sign (f (x + π) = -f x) has a zero; this is the IVT step of the median bisection. -/
theorem planar_necklace_continuous_odd_exists_zero (f : ℝ → ℝ) (hf : Continuous f)
    (hodd : ∀ x, f (x + Real.pi) = - f x) : ∃ x, f x = 0 := by
  by_cases h0 : f 0 = 0
  · exact ⟨0, h0⟩
  · have hpi : f Real.pi = - f 0 := by simpa using hodd 0
    have hcont : ContinuousOn f (Set.Icc 0 Real.pi) := hf.continuousOn
    have hle : (0 : ℝ) ≤ Real.pi := le_of_lt Real.pi_pos
    rcases lt_or_gt_of_ne h0 with hneg | hpos
    · have hmem : (0 : ℝ) ∈ Set.Ioo (f 0) (f Real.pi) := by
        constructor
        · exact hneg
        · rw [hpi]
          linarith
      obtain ⟨x, hxmem, hx⟩ := intermediate_value_Ioo hle hcont hmem
      exact ⟨x, hx⟩
    · have hmem : (0 : ℝ) ∈ Set.Ioo (f Real.pi) (f 0) := by
        constructor
        · rw [hpi]
          linarith
        · exact hpos
      obtain ⟨x, hxmem, hx⟩ := intermediate_value_Ioo' hle hcont hmem
      exact ⟨x, hx⟩
