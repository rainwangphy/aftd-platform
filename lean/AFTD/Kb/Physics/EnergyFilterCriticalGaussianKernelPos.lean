import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterCriticalGaussianKernel

/-!
# energy_filter_critical_gaussian_kernel_pos

Topic: statistical_mechanics   Node: e7af5717f1bf

Provenance: original. Related work: arXiv:2405.02158, Energy-filtered quantum states and the emergence of non-local correlations

The critical Gaussian kernel energy_filter_critical_gaussian_kernel x is strictly positive for all real x.
-/

/-- The critical Gaussian kernel is strictly positive for all real x. -/
theorem energy_filter_critical_gaussian_kernel_pos (x : ℝ) :
    0 < energy_filter_critical_gaussian_kernel x := by
  unfold energy_filter_critical_gaussian_kernel
  positivity
