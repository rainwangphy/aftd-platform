import AFTD.Prelude

/-!
# rademacher_filter_expected_purity_constant_tendsto

Topic: statistical_mechanics   Node: 53e1bce42743

Provenance: original. Related work: knowledgebase: OP-1152

The sequence (2 / sqrt(pi)) * (2 - 1 / m) converges to 4 / sqrt(pi) as m tends to infinity.
-/

/-- As m tends to infinity, the expected purity constant prefactor (2/sqrt(pi)) * (2 - 1/m) converges to 4/sqrt(pi). -/
theorem rademacher_filter_expected_purity_constant_tendsto :
    Filter.Tendsto (fun m : ℕ => (2 / Real.sqrt Real.pi) * (2 - 1 / (m : ℝ))) Filter.atTop (nhds (4 / Real.sqrt Real.pi)) := by
  have h_sub : Filter.Tendsto (fun m : ℕ => 2 - 1 / (m : ℝ)) Filter.atTop (nhds 2) := by
    simpa using tendsto_const_nhds.sub (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h_mul := h_sub.const_mul (2 / Real.sqrt Real.pi)
  have h_eq : (2 / Real.sqrt Real.pi) * 2 = 4 / Real.sqrt Real.pi := by ring
  rwa [h_eq] at h_mul
