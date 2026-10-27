import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RedistributionDiskToHalfplane

/-!
# redistribution_disk_to_halfplane_analytic

Topic: mechanism_design   Node: 264614ceaff4

Provenance: helper lemma. Uniform helper for IN-251, the proof of arXiv:2610.10995 Lemmas4.2/4.3. The disk logarithmic mean theorem and logarithm series already exist in the installed Mathlib; the upper-half-plane boundary passage, singular cosine integral and main harmonic bound remain unresolved. No research advance.

For any real y and radius r<1, the disk map is analytic on a neighbourhood of the closed disk of centre zero and radius r.
-/

open Finset Real MeasureTheory Metric MeromorphicOn

theorem redistribution_disk_to_halfplane_analytic
    (y r : ℝ) (hr : r < 1) :
    AnalyticOnNhd ℂ (redistribution_disk_to_halfplane y) (closedBall 0 r) := by
  intro z hz
  have hnorm : ‖z‖ < 1 := by
    have hh : ‖z‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hz
    linarith
  have hz1 : (1 : ℂ)-z ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    rw [← he, norm_one] at hnorm
    linarith
  change AnalyticAt ℂ (fun w : ℂ => (y : ℂ) * Complex.I * (1+w) / (1-w)) z
  fun_prop
