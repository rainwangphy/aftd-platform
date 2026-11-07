import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterCriticalGaussianKernel
import AFTD.Kb.Physics.EnergyFilterCriticalWindowIntegral

/-!
# energy_filter_critical_overlap_integral

Topic: statistical_mechanics   Node: 6958d6a3bc31

Provenance: original. Related work: arXiv:2405.02158, Energy-filtered quantum states and the emergence of non-local correlations

For width c, energy_filter_critical_overlap_integral c is the integral over the real line of the product of the critical Gaussian kernel and the window integral.
-/

open MeasureTheory in
/-- The overlap integral D_c = integral_R g(x) F_c(x) dx in the critical energy-filter purity formula. -/
noncomputable def energy_filter_critical_overlap_integral (c : ℝ) : ℝ := ∫ x : ℝ, energy_filter_critical_gaussian_kernel x * energy_filter_critical_window_integral c x
