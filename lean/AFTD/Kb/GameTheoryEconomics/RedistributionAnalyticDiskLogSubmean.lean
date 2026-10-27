import AFTD.Prelude

/-!
# redistribution_analytic_disk_log_submean

Topic: mechanism_design   Node: a10b45aac198

Provenance: helper lemma. Uniform helper for IN-251, the proof of arXiv:2610.10995 Lemmas4.2/4.3. The disk logarithmic mean theorem and logarithm series already exist in the installed Mathlib; the upper-half-plane boundary passage, singular cosine integral and main harmonic bound remain unresolved. No research advance.

For a complex function analytic on a neighbourhood of a closed disk of positive radius, with nonzero value at its centre, the logarithm of the central norm is at most the circle average of the logarithmic norm.
-/

open Finset Real MeasureTheory Metric MeromorphicOn

theorem redistribution_analytic_disk_log_submean
    (f : ℂ → ℂ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hfc : f c ≠ 0) :
    Real.log ‖f c‖ ≤ Real.circleAverage (fun z => Real.log ‖f z‖) c R := by
  have hfa : AnalyticOnNhd ℂ f (closedBall c |R|) := by
    simpa only [abs_of_pos hR] using hf
  rw [hfa.circleAverage_log_norm (ne_of_gt hR) hfc]
  suffices 0 ≤ ∑ᶠ u, divisor f (closedBall c |R|) u *
      Real.log (R * ‖c-u‖⁻¹) by linarith
  apply finsum_nonneg
  intro u
  by_cases hu : u ∈ closedBall c |R|
  · by_cases he : u=c
    · subst u
      rw [hfa.divisor_apply (by simp),
        (hfa c (by simp)).analyticOrderAt_eq_zero.mpr hfc]
      simp
    · apply mul_nonneg (by exact_mod_cast hfa.divisor_nonneg u)
      apply Real.log_nonneg
      have hnu : 0 < ‖c-u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm he))
      have hle : ‖c-u‖ ≤ R := by
        simpa only [mem_closedBall, dist_eq_norm', abs_of_pos hR] using hu
      rw [← div_eq_mul_inv]
      exact (one_le_div hnu).mpr hle
  · rw [(divisor f (closedBall c |R|)).apply_eq_zero_of_notMem hu]
    simp
