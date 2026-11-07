import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterCriticalGaussianKernel

/-!
# energy_filter_critical_window_integral

Topic: statistical_mechanics   Node: 6f6963e1942f

Provenance: original. Related work: arXiv:2405.02158, Energy-filtered quantum states and the emergence of non-local correlations

For width c and point x, energy_filter_critical_window_integral c x is the interval integral of the critical Gaussian kernel from -c - x to -x.
-/

open MeasureTheory in
/-- The window integral F_c(x) = integral_{-c-x}^{-x} g(y) dy of the Gaussian kernel over an interval of width c. -/
noncomputable def energy_filter_critical_window_integral (c x : ℝ) : ℝ := ∫ y in (-c - x)..(-x), energy_filter_critical_gaussian_kernel y
