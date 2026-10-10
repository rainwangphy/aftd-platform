import AFTD.Prelude

/-!
# InnerProductSpace.pow_mul_exp_bddAbove

Topic: classical_mechanics   Node: 7cb34ff88f41

Provenance: formalization of a published result. Source: Physlib, `InnerProductSpace.pow_mul_exp_bddAbove`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/InnerProductSpace/Gaussian.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

InnerProductSpace.pow_mul_exp_bddAbove
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ContinuousLinearMap Filter RCLike Real SchwartzMap in
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D] in
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
variable (𝕜 : Type*) [RCLike 𝕜] in
variable (B : D ≃L[ℝ] E) (x₀ x : E) in
lemma InnerProductSpace.pow_mul_exp_bddAbove {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    ∃ C > 0, ∀ x ≥ 0, x ^ s * (2 + x) ^ n * rexp (-2⁻¹ * x) ≤ C := by
  let b : ℝ → ℝ := fun x ↦ x ^ s * (2 + x) ^ n * rexp (-2⁻¹ * x)
  have hb : Continuous b := by fun_prop
  have htop : Tendsto b atTop (nhds 0) := by
    let g : ℝ → ℝ := fun x : ℝ ↦ x ^ (s + n) * rexp (-2⁻¹ * x)
    let g' : ℝ → ℝ := fun x ↦ 2 + x
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := 0) (h := exp 1 • g ∘ g') ?_ ?_ ?_ ?_
    · exact tendsto_const_nhds
    · rw [← smul_zero (exp 1)]
      refine Tendsto.const_smul ?_ _
      refine Tendsto.comp (y := atTop) ?_ ?_
      · exact tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s + n) 2⁻¹ (by norm_num)
      · exact tendsto_atTop_atTop.mpr fun x ↦ ⟨x - 2, by simp [g', add_comm]⟩
    · exact eventually_atTop.mpr ⟨0, fun _ _ ↦ by positivity⟩
    · refine eventually_atTop.mpr ⟨0, fun x hx ↦ ?_⟩
      simp only [b, g, g', Function.comp_def, Pi.smul_def, mul_add, exp_add, smul_eq_mul]
      field_simp
      simp only [exp_neg, rpow_add (show 0 < 2 + x by linarith), rpow_natCast]
      field_simp
      exact rpow_le_rpow hx (by linarith) hs
  have htail : ∀ᶠ x in atTop, b x < 1 :=
    (htop.eventually <| isOpen_Ioo.mem_nhds ⟨neg_one_lt_zero, zero_lt_one⟩).mono fun _ h ↦ h.2
  obtain ⟨M, hgM⟩ := eventually_atTop.mp htail
  obtain ⟨x₀, hx₀, hx₀'⟩ :=
    isCompact_Icc.exists_isMaxOn ⟨0, Set.left_mem_Icc.mpr (abs_nonneg M)⟩ hb.continuousOn
  refine ⟨max (b x₀) 1, by simp, fun x hx ↦ ?_⟩
  by_cases hxM : x ≤ |M|
  · exact le_max_of_le_left (hx₀' ⟨hx, hxM⟩)
  · exact le_max_of_le_right (hgM x <| (le_abs_self _).trans (Std.le_of_not_ge hxM)).le
