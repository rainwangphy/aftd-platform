import AFTD.Prelude

/-!
# tendsto_pow_two_div_sub_two_atTop

Topic: combinatorics   Node: efcd686b5da3

Provenance: helper lemma. step towards four_cycle_graph_code_density_tendsto_one_along_powers_of_two

As the natural number r tends to infinity, 2^r / (2^r - 2) tends to 1.
-/

/-- The sequence 2^r / (2^r - 2) tends to 1 as r tends to infinity. -/
theorem tendsto_pow_two_div_sub_two_atTop :
    Filter.Tendsto (fun r : ℕ => ((2 : ℝ) ^ r) / (((2 : ℝ) ^ r) - 2)) Filter.atTop (nhds 1) := by
  have hpow : Filter.Tendsto (fun r : ℕ => (2 : ℝ) ^ r) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hden : Filter.Tendsto (fun r : ℕ => (2 : ℝ) ^ r - 2) Filter.atTop Filter.atTop := by
    have h := Filter.tendsto_atTop_add_const_right Filter.atTop (-2 : ℝ) hpow
    simpa [sub_eq_add_neg] using h
  have hfrac : Filter.Tendsto (fun r : ℕ => 2 / ((2 : ℝ) ^ r - 2)) Filter.atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop hden 2
  have hone : Filter.Tendsto (fun r : ℕ => 1 + 2 / ((2 : ℝ) ^ r - 2)) Filter.atTop (nhds 1) := by
    simpa using Filter.Tendsto.const_add (1 : ℝ) hfrac
  refine Filter.Tendsto.congr' ?_ hone
  change ∀ᶠ r : ℕ in Filter.atTop, 1 + 2 / ((2 : ℝ) ^ r - 2) = (2 : ℝ) ^ r / ((2 : ℝ) ^ r - 2)
  rw [Filter.eventually_atTop]
  use 2
  intro r hr
  have hden' : ((2 : ℝ) ^ r - 2) ≠ 0 := by
    have h2 : (2 : ℝ) ^ r ≥ (2 : ℝ) ^ 2 := pow_le_pow_right₀ (by norm_num) hr
    norm_num at h2 ⊢
    linarith
  field_simp [hden']
  ring
