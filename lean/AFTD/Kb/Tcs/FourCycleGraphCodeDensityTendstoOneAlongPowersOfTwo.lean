import AFTD.Prelude
import AFTD.Kb.Tcs.KstCodeMaxDensity
import AFTD.Kb.Tcs.K22CodeMaxDensityLe
import AFTD.Kb.Tcs.TendstoPowTwoDivSubTwoAtTop
import AFTD.Kb.Tcs.K22CodeMaxDensityTwoPowGe

/-!
# four_cycle_graph_code_density_tendsto_one_along_powers_of_two

Topic: combinatorics   Node: 12f67343196c

Provenance: formalization of a published result. Source: arXiv:2610.35136, Proposition 4.3; arXiv:2301.13305, Proposition 1.5

As the natural number r tends to infinity, the sequence ((2 : ℝ) ^ r) * kst_code_max_density 2 2 (2 ^ r) tends to 1.
-/

/-- The sequence 2^r * kst_code_max_density 2 2 (2^r) converges to 1 as r tends to infinity. -/
theorem four_cycle_graph_code_density_tendsto_one_along_powers_of_two :
    Filter.Tendsto (fun r : ℕ => ((2 : ℝ) ^ r) * kst_code_max_density 2 2 (2 ^ r)) Filter.atTop (nhds 1) := by
  have h_const : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) := tendsto_const_nhds
  have h_top := tendsto_pow_two_div_sub_two_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h_const h_top
  · filter_upwards [Filter.eventually_ge_atTop 2] with r hr
    have h_ge := k22_code_max_density_two_pow_ge r hr
    have h_pos : 0 < (2 : ℝ) ^ r := by positivity
    have h_mul := mul_le_mul_of_nonneg_left h_ge (le_of_lt h_pos)
    rw [mul_one_div_cancel (ne_of_gt h_pos)] at h_mul
    exact h_mul
  · filter_upwards [Filter.eventually_ge_atTop 2] with r hr
    have hr4 : 4 ≤ 2 ^ r := by
      calc
        4 = 2 ^ 2 := by rfl
        _ ≤ 2 ^ r := Nat.pow_le_pow_right (by decide) hr
    have h_le := k22_code_max_density_le (2 ^ r) hr4
    have h_pos : 0 ≤ (2 : ℝ) ^ r := by positivity
    have h_mul := mul_le_mul_of_nonneg_left h_le h_pos
    have h_eq : (2 : ℝ) ^ r * (1 / (((2 ^ r : ℕ) : ℝ) - 2)) = (2 : ℝ) ^ r / ((2 : ℝ) ^ r - 2) := by
      push_cast
      ring
    rwa [h_eq] at h_mul
