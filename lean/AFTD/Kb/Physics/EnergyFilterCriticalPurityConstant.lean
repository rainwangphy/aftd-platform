import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterCriticalGaussianKernel
import AFTD.Kb.Physics.EnergyFilterCriticalWindowIntegral
import AFTD.Kb.Physics.EnergyFilterCriticalOverlapIntegral

/-!
# energy_filter_critical_purity_constant

Topic: statistical_mechanics   Node: 1e782a33c5a0

Provenance: original. Related work: arXiv:2405.02158, Energy-filtered quantum states and the emergence of non-local correlations

For width c, energy_filter_critical_purity_constant c is the crossover purity constant K(c) given by twice the integral of g(x)^2 * F_c(x)^2 over the square of the overlap integral D_c.
-/

open MeasureTheory in
/-- The critical purity constant K(c) = 2 integral_R g(x)^2 F_c(x)^2 dx / D_c^2 for random signed energy filters. -/
noncomputable def energy_filter_critical_purity_constant (c : ℝ) : ℝ := 2 * (∫ x : ℝ, (energy_filter_critical_gaussian_kernel x)^2 * (energy_filter_critical_window_integral c x)^2) /
    (energy_filter_critical_overlap_integral c)^2
