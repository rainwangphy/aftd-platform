import AFTD.Prelude
import AFTD.Kb.Tcs.ComplexLaplaceIntegrand
import AFTD.Kb.Tcs.ComplexLaplaceEnvelope

/-!
# norm_complexLaplaceIntegrand_le_envelope

Topic: quantum   Node: 0f0791772067

Provenance: formalization of a published result. Source: QuantumInfo, `norm_complexLaplaceIntegrand_le_envelope`. Lean proof by Dennj Osele, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/ComplexLaplaceTransform.lean (Copyright (c) 2025 Dennj Osele. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

norm_complexLaplaceIntegrand_le_envelope
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
theorem norm_complexLaplaceIntegrand_le_envelope
    {α : Type*} {E : α → WithTop ℝ} {z w : ℂ} {δ : ℝ}
    (hw : w ∈ Metric.closedBall z δ) (x : α) :
    ‖ComplexLaplaceIntegrand E w x‖ ≤ ComplexLaplaceEnvelope E z δ x := by
  unfold ComplexLaplaceEnvelope ComplexLaplaceIntegrand
  by_cases h : E x = ⊤
  · simp [h]
  · simp only [h, dite_false]
    set e : ℝ := (E x).untop h
    have hdist : ‖w - z‖ ≤ δ := by
      simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hw
    have hre_abs : |w.re - z.re| ≤ δ := by
      exact (Complex.abs_re_le_norm (w - z)).trans (by simpa [Complex.sub_re] using hdist)
    rw [Complex.norm_exp, Complex.norm_exp, Complex.norm_exp]
    rcases le_total 0 e with he | he
    · refine le_add_of_le_of_nonneg ?_ (Real.exp_pos _).le
      exact Real.exp_le_exp.mpr (by
        simp only [neg_mul, Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, sub_zero, Complex.sub_re]
        nlinarith [abs_le.mp hre_abs |>.1])
    · refine le_add_of_nonneg_of_le (Real.exp_pos _).le ?_
      exact Real.exp_le_exp.mpr (by
        simp only [neg_mul, Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, sub_zero, Complex.add_re]
        nlinarith [abs_le.mp hre_abs |>.2])
