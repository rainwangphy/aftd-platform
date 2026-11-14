import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterAbsConvolutionControl

/-!
# energy_filter_sequence_convolution_pointwise_summable

Topic: statistical_mechanics   Node: d5b1c0d204ca

Provenance: helper lemma. step towards summable_energy_filters_universal_lattice_purity_constant

For a square-summable a and any m, the convolution series sum_j a j * a (m - j) is absolutely summable.
-/

/-- The discrete convolution is well defined pointwise, so the inner series in the fourth lattice sum is a genuine convergent series. -/
theorem energy_filter_sequence_convolution_pointwise_summable (a : ℤ → ℝ) (ha_lp : Memℓp a (4 / 3))
    (m : ℤ) : Summable (fun j : ℤ => a j * a (m - j)) := by
  exact ((energy_filter_abs_convolution_control a ha_lp).1 m).of_abs
