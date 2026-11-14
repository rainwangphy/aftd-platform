import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialWeight

/-!
# energy_filter_floor_kernel_measurable

Topic: statistical_mechanics   Node: 986f709ae371

Provenance: helper lemma. OP-892: direct shifted-binomial kernel limit and uniform bound.

For every k and integer shifts, the four-factor floor-scaled centered binomial product is a measurable real function.
-/

theorem energy_filter_floor_kernel_measurable (k : ℕ) (u v w : ℤ) :
    Measurable (fun x : ℝ => let t := Int.floor (Real.sqrt (k:ℝ)*x)
      energy_filter_centered_binomial_weight k t *
      energy_filter_centered_binomial_weight k (t+u) *
      energy_filter_centered_binomial_weight k (t+v) *
      energy_filter_centered_binomial_weight k (t+w)) := by
  have hflo : Measurable (fun x : ℝ => Int.floor (Real.sqrt (k:ℝ)*x)) :=
    Int.measurable_floor.comp (measurable_const.mul measurable_id)
  have hweight : Measurable (energy_filter_centered_binomial_weight k) := measurable_of_countable _
  exact (((hweight.comp hflo).mul (hweight.comp (hflo.add measurable_const))).mul
    (hweight.comp (hflo.add measurable_const))).mul (hweight.comp (hflo.add measurable_const))
