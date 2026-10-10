import AFTD.Prelude
import AFTD.Kb.Physics.InnerProductSpacePowMulExpBddAbove
import AFTD.Kb.Physics.InnerProductSpaceNormIteratedFDerivInnerSLLePow

/-!
# InnerProductSpace.realStdGaussian

Topic: classical_mechanics   Node: afe5cf0053de

Provenance: formalization of a published result. Source: Physlib, `InnerProductSpace.realStdGaussian`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/InnerProductSpace/Gaussian.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The (unnormalized) real-valued standard Gaussian `exp (-2⁻¹ * ‖x‖ ^ 2)` as a Schwartz map. This definition is used to construct the general RCLike-valued Gaussian and the preferred version to use is `gaussian ℝ B x₀` (or `stdGaussian E ℝ` for mean zero, variance one).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open InnerProductSpace in
open ContinuousLinearMap Filter RCLike Real SchwartzMap in
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D] in
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
variable (𝕜 : Type*) [RCLike 𝕜] in
variable (B : D ≃L[ℝ] E) (x₀ x : E) in
variable (E) in
/-- The (unnormalized) real-valued standard Gaussian `exp (-2⁻¹ * ‖x‖ ^ 2)` as a Schwartz map. This definition is used to construct the general RCLike-valued Gaussian and the preferred version to use is `gaussian ℝ B x₀` (or `stdGaussian E ℝ` for mean zero, variance one). -/
noncomputable def InnerProductSpace.realStdGaussian : 𝓢(E, ℝ) where
  toFun x := rexp (-2⁻¹ * ‖x‖ ^ 2)
  smooth' := contDiff_exp.fun_comp <| contDiff_const.mul <| contDiff_norm_sq ℝ
  decay' k n := by
    obtain ⟨C, hC, hbC⟩ := pow_mul_exp_bddAbove (show 0 ≤ (k / 2 : ℝ) by positivity) n
    use n.factorial * C
    intro x
    calc
      _ = ‖x‖ ^ k * ‖iteratedFDeriv ℝ n ((fun x ↦ rexp (-2⁻¹ * x)) ∘ fun x ↦ innerSL ℝ x x) x‖ := by
        simp [Function.comp_def]
      _ ≤ ‖x‖ ^ k * (n.factorial * rexp (-2⁻¹ * innerSL ℝ x x) * (2 + ‖x‖ ^ 2) ^ n) := by
        refine mul_le_mul_of_nonneg_left ?_ (by simp)
        refine norm_iteratedFDeriv_comp_le (by fun_prop) ?_ (Nat.cast_le.mpr n.le_succ) x ?_ ?_
        · simp [contDiff_norm_sq ℝ]
        · intro m _
          simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_exp_const_mul,
            norm_mul, norm_eq_abs, abs_exp, norm_pow, norm_neg, norm_inv, inv_pow, Nat.abs_ofNat]
          refine mul_le_of_le_one_left (exp_nonneg _) ?_
          exact inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two)
        · exact fun m hm _ ↦ norm_iteratedFDeriv_innerSL_le_pow x hm
      _ = n.factorial * ((‖x‖ ^ 2) ^ (k / 2 : ℝ) * (2 + ‖x‖ ^ 2) ^ n * rexp (-2⁻¹ * ‖x‖ ^ 2)) := by
        rw [← rpow_natCast_mul (norm_nonneg _)]
        field_simp
        simp
      _ ≤ n.factorial * C :=
        mul_le_mul_of_nonneg_left (hbC _ <| pow_two_nonneg ‖x‖) (Nat.cast_nonneg' _)
