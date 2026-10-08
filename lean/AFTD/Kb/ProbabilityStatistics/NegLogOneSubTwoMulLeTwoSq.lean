import AFTD.Prelude
import AFTD.Kb.ProbabilityStatistics.TaylorAuxHasDerivAt
import AFTD.Kb.ProbabilityStatistics.TaylorAuxZero

/-!
# neg_log_one_sub_two_mul_le_two_sq

Topic: concentration   Node: 3538f9147e75

Provenance: helper lemma. TCSlib, `neg_log_one_sub_two_mul_le_two_sq`. Lean proof by Ganesh Sankar, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/JohnsonLindenstrauss/ChiSquaredMGF.lean (Copyright (c) 2026 Ganesh Sankar. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Taylor bound for the centered chi-squared log-MGF. For every real number $s$ with $\abs{s} \le 1/4$, one has
\[
  -s - \tfrac{1}{2}\log(1 - 2s) \;\le\; 2s^2 .
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset in
variable {d k : ℕ} in
/-- **Taylor bound** for the centered chi-squared log-MGF: for every real `s` with `|s| ≤ 1/4`, `−s − (1/2) log(1 − 2s) ≤ 2s²`. This is the log-MGF estimate in [LM00, proof of Lemma 1]. Deviation from the source: Laurent–Massart prove `−s − ½ log(1 − 2s) ≤ s²/(1 − 2s)` for `0 ≤ s < 1/2`; we restrict to `|s| ≤ 1/4`, where `s²/(1 − 2s) ≤ 2s²`, and also cover negative `s` (needed for the two-sided Bernstein bound). **Proof sketch.** Substitute `u = 2s`, so `|u| ≤ 1/2`, and set `f(u) = u² + u + log(1 − u)`; the claim is `f(u) ≥ 0 = f(0)`. Step 1: `f` is continuous on `[−1/2, 1/2]` and differentiable on its interior, with derivative `u(1 − 2u)/(1 − u)` (`taylorAux_hasDerivAt`). Step 2: the derivative is nonnegative on `[0, 1/2]`, so `f` is monotone there. Step 3: the derivative is nonpositive on `[−1/2, 0]`, so `f` is antitone there. Step 4: split on the sign of `u`; in either case `f(u) ≥ f(0) = 0` (`taylorAux_zero`). Step 5: unfold `f(2s) = 4s² + 2s + log(1 − 2s) ≥ 0` and rearrange. -/
lemma neg_log_one_sub_two_mul_le_two_sq (s : ℝ) (hs : |s| ≤ 1 / 4) :
    -s - (1/2) * Real.log (1 - 2*s) ≤ 2 * s^2 := by
  -- Equivalent: 2s² + s + (1/2) log(1-2s) ≥ 0.
  -- Set u = 2s, |u| ≤ 1/2. Want f(u) := u² + u + log(1-u) ≥ 0 = f(0).
  set f : ℝ → ℝ := fun x => x ^ 2 + x + Real.log (1 - x)
  have hf_zero : f 0 = 0 := taylorAux_zero
  have h_abs : |2*s| ≤ 1/2 := by
    rw [abs_mul]; simp only [abs_two]; linarith [abs_nonneg s]
  have h_two_s : (2*s : ℝ) ∈ Set.Icc (-(1/2 : ℝ)) (1/2) :=
    abs_le.mp h_abs
  -- Step 1: shared analytic scaffolding on the full interval `[-1/2, 1/2]`:
  -- `f` is continuous there (`1 - x > 0`) and differentiable on the interior.
  have hcont : ContinuousOn f (Set.Icc (-(1/2 : ℝ)) (1/2)) := by
    intro x hx
    simp only [Set.mem_Icc] at hx
    have h1mx : 0 < 1 - x := by linarith
    refine (continuous_pow 2).continuousAt.add ?_ |>.add ?_ |>.continuousWithinAt
    · exact continuousAt_id
    · exact (Real.continuousAt_log h1mx.ne').comp
        (continuous_const.sub continuous_id).continuousAt
  have hdiff : DifferentiableOn ℝ f (Set.Ioo (-(1/2 : ℝ)) (1/2)) := by
    intro x hx
    simp only [Set.mem_Ioo] at hx
    exact (taylorAux_hasDerivAt x (by linarith)).differentiableAt.differentiableWithinAt
  -- Step 2: monotone on `[0, 1/2]`, since `f'(u) = u(1-2u)/(1-u) ≥ 0` there.
  have h_mono : MonotoneOn f (Set.Icc (0 : ℝ) (1/2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact hcont.mono (Set.Icc_subset_Icc (by norm_num) le_rfl)
    · rw [interior_Icc]
      exact hdiff.mono (Set.Ioo_subset_Ioo (by norm_num) le_rfl)
    · intro x hx
      rw [interior_Icc] at hx
      simp only [Set.mem_Ioo] at hx
      rw [(taylorAux_hasDerivAt x (by linarith)).deriv]
      have h1 : 0 ≤ x := hx.1.le
      have h2 : 0 ≤ 1 - 2 * x := by linarith
      have h3 : 0 < 1 - x := by linarith
      positivity
  -- Step 3: antitone on `[-1/2, 0]`, since `f'(u) ≤ 0` there.
  have h_anti : AntitoneOn f (Set.Icc (-(1/2 : ℝ)) 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · exact hcont.mono (Set.Icc_subset_Icc le_rfl (by norm_num))
    · rw [interior_Icc]
      exact hdiff.mono (Set.Ioo_subset_Ioo le_rfl (by norm_num))
    · intro x hx
      rw [interior_Icc] at hx
      simp only [Set.mem_Ioo] at hx
      rw [(taylorAux_hasDerivAt x (by linarith)).deriv]
      have h1 : x ≤ 0 := hx.2.le
      have h2 : 0 < 1 - 2 * x := by linarith
      have h3 : 0 < 1 - x := by linarith
      have h_num : x * (1 - 2 * x) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h1 h2.le
      exact div_nonpos_of_nonpos_of_nonneg h_num h3.le
  -- Step 4: sign split — `f(2s) ≥ f(0) = 0` on either side of `0`.
  have h_nonneg : 0 ≤ f (2*s) := by
    by_cases h : 0 ≤ 2*s
    · -- 2s ∈ [0, 1/2]
      have h0_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (1/2) := by
        simp
      have h2s_mem : (2*s) ∈ Set.Icc (0 : ℝ) (1/2) := by
        refine ⟨h, ?_⟩
        linarith [h_two_s.2]
      have : f 0 ≤ f (2*s) := h_mono h0_mem h2s_mem h
      linarith [hf_zero]
    · -- 2s ∈ [-1/2, 0)
      push_neg at h
      have h0_mem : (0 : ℝ) ∈ Set.Icc (-(1/2 : ℝ)) 0 := by
        constructor
        · linarith
        · rfl
      have h2s_mem : (2*s) ∈ Set.Icc (-(1/2 : ℝ)) 0 := ⟨h_two_s.1, h.le⟩
      have : f 0 ≤ f (2*s) := h_anti h2s_mem h0_mem h.le
      linarith [hf_zero]
  -- Step 5: conclude — `f(2s) = 4s² + 2s + log(1-2s) ≥ 0`, divide by 2 and rearrange.
  have hf2s : f (2*s) = (2*s)^2 + 2*s + Real.log (1 - 2*s) := rfl
  have : 0 ≤ (2*s)^2 + 2*s + Real.log (1 - 2*s) := hf2s ▸ h_nonneg
  nlinarith
