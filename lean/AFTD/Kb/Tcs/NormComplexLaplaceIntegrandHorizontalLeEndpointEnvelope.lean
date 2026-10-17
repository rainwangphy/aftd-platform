import AFTD.Prelude
import AFTD.Kb.Tcs.ComplexLaplaceIntegrand
import AFTD.Kb.Tcs.ComplexLaplaceEndpointEnvelope

/-!
# norm_complexLaplaceIntegrand_horizontal_le_endpointEnvelope

Topic: quantum   Node: ded83896627f

Provenance: formalization of a published result. Source: QuantumInfo, `norm_complexLaplaceIntegrand_horizontal_le_endpointEnvelope`. Lean proof by Dennj Osele, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/ComplexLaplaceTransform.lean (Copyright (c) 2025 Dennj Osele. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

norm_complexLaplaceIntegrand_horizontal_le_endpointEnvelope
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
theorem norm_complexLaplaceIntegrand_horizontal_le_endpointEnvelope
    {α : Type*} {E : α → WithTop ℝ} {a b : ℂ} {t : ℝ}
    (ht : t ∈ Set.uIcc a.re b.re) (x : α) :
    ‖ComplexLaplaceIntegrand E (t + a.im * Complex.I) x‖ ≤
      ComplexLaplaceEndpointEnvelope E a (b.re + a.im * Complex.I) x := by
  unfold ComplexLaplaceEndpointEnvelope ComplexLaplaceIntegrand
  by_cases h : E x = ⊤
  · simp [h]
  · simp only [h, dite_false]
    set e : ℝ := (E x).untop h
    rw [Complex.norm_exp, Complex.norm_exp, Complex.norm_exp]
    rcases Set.mem_uIcc.mp ht with ⟨hat, htb⟩ | ⟨hbt, hta⟩ <;> rcases le_total 0 e with he | he
    · refine le_add_of_le_of_nonneg ?_ (Real.exp_pos _).le
      exact Real.exp_le_exp.mpr (by
        simp only [neg_mul, Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, sub_zero, Complex.add_re, Complex.I_re]
        nlinarith)
    · refine le_add_of_nonneg_of_le (Real.exp_pos _).le ?_
      exact Real.exp_le_exp.mpr (by
        simp only [neg_mul, Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, sub_zero, Complex.add_re, Complex.I_re]
        nlinarith)
    · refine le_add_of_nonneg_of_le (Real.exp_pos _).le ?_
      exact Real.exp_le_exp.mpr (by
        simp only [neg_mul, Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, sub_zero, Complex.add_re, Complex.I_re]
        nlinarith)
    · refine le_add_of_le_of_nonneg ?_ (Real.exp_pos _).le
      exact Real.exp_le_exp.mpr (by
        simp only [neg_mul, Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, sub_zero, Complex.add_re, Complex.I_re]
        nlinarith)
