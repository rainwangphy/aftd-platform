import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterAbsConvolutionControl

/-!
# energy_filter_sequence_lattice_s4_summable

Topic: statistical_mechanics   Node: acb640a82dcc

Provenance: helper lemma. step towards summable_energy_filters_universal_lattice_purity_constant

If a is in l^{4/3} then the squared convolution (a*a)(m)^2 is summable over m, i.e. a*a is square-summable, so the fourth lattice sum is a genuine convergent series.
-/

/-- The fourth lattice sum converges: the convolution of an l^{4/3} sequence with itself lies in l^2. -/
theorem energy_filter_sequence_lattice_s4_summable (a : ℤ → ℝ) (ha_lp : Memℓp a (4 / 3)) :
    Summable (fun m : ℤ => (∑' j : ℤ, a j * a (m - j)) ^ 2) := by
  have hconv_abs := (energy_filter_abs_convolution_control a ha_lp).1
  have hconv2' := (energy_filter_abs_convolution_control a ha_lp).2
  apply hconv2'.of_nonneg_of_le
  · intro m; exact sq_nonneg _
  · intro m
    have hmajor : |∑' j : ℤ, a j * a (m-j)| ≤ ∑' j : ℤ, |a j * a (m-j)| := by
      have hh := norm_tsum_le_tsum_norm (show Summable (fun j : ℤ => ‖a j * a (m-j)‖) by
        simpa only [Real.norm_eq_abs] using hconv_abs m)
      simpa only [Real.norm_eq_abs] using hh
    have hnonneg : 0 ≤ ∑' j : ℤ, |a j * a (m-j)| := tsum_nonneg fun j => abs_nonneg _
    have hh := (sq_le_sq₀ (abs_nonneg _) hnonneg).2 hmajor
    simpa only [sq_abs] using hh
