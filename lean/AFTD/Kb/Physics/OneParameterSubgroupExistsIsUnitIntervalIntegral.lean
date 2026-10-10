import AFTD.Prelude

/-!
# OneParameterSubgroup.exists_isUnit_intervalIntegral

Topic: classical_mechanics   Node: 8a04f7a4fbdb

Provenance: formalization of a published result. Source: Physlib, `OneParameterSubgroup.exists_isUnit_intervalIntegral`. Lean proof by Tom Ole Diem, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/OneParameterSubgroups/Basic.lean (Copyright (c) 2026 Tom Ole Diem. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

OneParameterSubgroup.exists_isUnit_intervalIntegral
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter Topology in
variable {E : Type*} [NormedRing E] [NormedAlgebra ℝ E] [CompleteSpace E] in
lemma OneParameterSubgroup.exists_isUnit_intervalIntegral [Nontrivial E] (U : AddChar ℝ E) (hU : Continuous U) :
    ∃ d : ℝ, 0 < d ∧ IsUnit (∫ x in (0 : ℝ)..d, U x) := by
  have hone : 0 < ‖(1 : E)‖ := norm_pos_iff.mpr one_ne_zero
  have hevent : ∀ᶠ x : ℝ in 𝓝 0, ‖U x - 1‖ < ‖(1 : E)‖⁻¹ / 2 := by
    have hmem : Set.Iio (‖(1 : E)‖⁻¹ / 2) ∈ 𝓝 ‖U 0 - 1‖ := by
      simpa using Iio_mem_nhds (by positivity : 0 < ‖(1 : E)‖⁻¹ / 2)
    exact (continuous_norm.comp (hU.sub continuous_const)).continuousAt hmem
  obtain ⟨r, hr, hrU⟩ := Metric.eventually_nhds_iff.mp hevent
  let d := r / 2
  have hd : 0 < d := by positivity
  let q : Eˣ := {
    val := d • 1
    inv := d⁻¹ • 1
    val_inv := by rw [smul_mul_smul_comm, mul_inv_cancel₀ hd.ne', one_smul, one_mul]
    inv_val := by rw [smul_mul_smul_comm, inv_mul_cancel₀ hd.ne', one_smul, one_mul] }
  refine ⟨d, hd, (Units.ofNearby q _ ?_).isUnit⟩
  calc
    _ = ‖(∫ x in (0 : ℝ)..d, U x) - d • (1 : E)‖ := rfl
    _ = ‖(∫ x in (0 : ℝ)..d, U x) - ∫ _x in (0 : ℝ)..d, (1 : E)‖ := by
      rw [intervalIntegral.integral_const, sub_zero]
    _ = ‖∫ x in (0 : ℝ)..d, (U x - 1)‖ := by
      rw [intervalIntegral.integral_sub (hU.intervalIntegrable 0 d)
        (continuous_const.intervalIntegrable 0 d)]
    _ ≤ (‖(1 : E)‖⁻¹ / 2) * |d - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => by
        apply le_of_lt
        apply hrU
        rw [Real.dist_0_eq_abs]
        rw [Set.uIoc_of_le hd.le] at hx
        rw [abs_of_nonneg hx.1.le]
        exact hx.2.trans_lt (by dsimp [d]; linarith))
    _ = (‖(1 : E)‖⁻¹ / 2) * d := by rw [sub_zero, abs_of_pos hd]
    _ < d * ‖(1 : E)‖⁻¹ := by nlinarith [inv_pos.mpr hone]
    _ = ‖q.inv‖⁻¹ := by simp [q, norm_smul, mul_comm, abs_of_pos hd]
