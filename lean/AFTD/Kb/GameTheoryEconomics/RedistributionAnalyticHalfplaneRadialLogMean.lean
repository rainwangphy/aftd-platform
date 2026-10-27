import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RedistributionAnalyticDiskLogSubmean
import AFTD.Kb.GameTheoryEconomics.RedistributionDiskToHalfplane
import AFTD.Kb.GameTheoryEconomics.RedistributionDiskToHalfplaneZero
import AFTD.Kb.GameTheoryEconomics.RedistributionDiskToHalfplaneAnalytic

/-!
# redistribution_analytic_halfplane_radial_log_mean

Topic: mechanism_design   Node: c6af8884c7da

Provenance: helper lemma. Uniform helper for IN-251, the proof of arXiv:2610.10995 Lemmas4.2/4.3. The disk logarithmic mean theorem and logarithm series already exist in the installed Mathlib; the upper-half-plane boundary passage, singular cosine integral and main harmonic bound remain unresolved. No research advance.

For an entire complex function f, any real y, and 0<r<1, if f(i*y) is nonzero, then log norm f(i*y) is at most the circle average of log norm f composed with the disk map on radius r. The boundary passage and the real-line Poisson kernel formula are not asserted.
-/

open Finset Real MeasureTheory Metric MeromorphicOn

theorem redistribution_analytic_halfplane_radial_log_mean
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f Set.univ)
    (y r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (hfc : f ((y : ℂ)*Complex.I) ≠ 0) :
    Real.log ‖f ((y : ℂ)*Complex.I)‖ ≤
      Real.circleAverage (fun z => Real.log ‖f (redistribution_disk_to_halfplane y z)‖) 0 r := by
  have hc : AnalyticOnNhd ℂ (fun z => f (redistribution_disk_to_halfplane y z))
      (closedBall 0 r) := by
    intro z hz
    exact (hf _ (Set.mem_univ _)).comp
      (redistribution_disk_to_halfplane_analytic y r hr1 z hz)
  have h0 : f (redistribution_disk_to_halfplane y 0) ≠ 0 := by
    simpa only [redistribution_disk_to_halfplane_zero] using hfc
  simpa only [redistribution_disk_to_halfplane_zero] using
    redistribution_analytic_disk_log_submean
      (fun z => f (redistribution_disk_to_halfplane y z)) 0 r hr0 hc h0
