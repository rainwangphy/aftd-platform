import AFTD.Prelude

/-!
# OneParameterSubgroup.mul_intervalIntegral_eq_sub

Topic: classical_mechanics   Node: c23dbba30e82

Provenance: formalization of a published result. Source: Physlib, `OneParameterSubgroup.mul_intervalIntegral_eq_sub`. Lean proof by Tom Ole Diem, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/OneParameterSubgroups/Basic.lean (Copyright (c) 2026 Tom Ole Diem. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Translating a one-parameter subgroup translates its interval integral.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter Topology in
variable {E : Type*} [NormedRing E] [NormedAlgebra ℝ E] [CompleteSpace E] in
/-- Translating a one-parameter subgroup translates its interval integral. -/
lemma OneParameterSubgroup.mul_intervalIntegral_eq_sub (U : AddChar ℝ E) (hU : Continuous U) (s t : ℝ) :
    U s * ∫ x in (0 : ℝ)..t, U x =
      (∫ x in (0 : ℝ)..(s + t), U x) - ∫ x in (0 : ℝ)..s, U x := by
  let L : E →L[ℝ] E :=
    (LinearMap.mulLeft ℝ (U s)).mkContinuous ‖U s‖ (fun x => norm_mul_le _ _)
  calc
    _ = L (∫ x in (0 : ℝ)..t, U x) := rfl
    _ = ∫ x in (0 : ℝ)..t, L (U x) :=
      (L.intervalIntegral_comp_comm (hU.intervalIntegrable 0 t)).symm
    _ = ∫ x in (0 : ℝ)..t, U (s + x) := by
      apply intervalIntegral.integral_congr
      intro x _
      exact (U.map_add_eq_mul s x).symm
    _ = ∫ x in s..(s + t), U x := by
      rw [intervalIntegral.integral_comp_add_left, add_zero]
    _ = (∫ x in (0 : ℝ)..(s + t), U x) - ∫ x in (0 : ℝ)..s, U x := by
      rw [eq_sub_iff_add_eq, add_comm]
      exact intervalIntegral.integral_add_adjacent_intervals
        (hU.intervalIntegrable 0 s) (hU.intervalIntegrable s (s + t))
