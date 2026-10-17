import AFTD.Prelude
import AFTD.Kb.Tcs.ComplexLaplaceIntegrand
import AFTD.Kb.Tcs.ComplexLaplaceEndpointEnvelope

/-!
# norm_complexLaplaceIntegrand_vertical_le_endpointEnvelope

Topic: quantum   Node: 8cba4c3dde32

Provenance: formalization of a published result. Source: QuantumInfo, `norm_complexLaplaceIntegrand_vertical_le_endpointEnvelope`. Lean proof by Dennj Osele, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/ComplexLaplaceTransform.lean (Copyright (c) 2025 Dennj Osele. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

norm_complexLaplaceIntegrand_vertical_le_endpointEnvelope
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
theorem norm_complexLaplaceIntegrand_vertical_le_endpointEnvelope
    {α : Type*} {E : α → WithTop ℝ} {a b : ℂ} {t : ℝ}
    (x : α) :
    ‖ComplexLaplaceIntegrand E (b.re + t * Complex.I) x‖ ≤
      ComplexLaplaceEndpointEnvelope E b (b.re + a.im * Complex.I) x := by
  unfold ComplexLaplaceEndpointEnvelope ComplexLaplaceIntegrand
  by_cases h : E x = ⊤
  · simp [h]
  · simp only [h, dite_false]
    rw [Complex.norm_exp, Complex.norm_exp, Complex.norm_exp]
    refine le_add_of_le_of_nonneg (le_of_eq ?_) (Real.exp_pos _).le
    congr 1
    simp only [neg_mul, Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_mul, sub_zero, add_zero, Complex.add_re, Complex.I_re]
