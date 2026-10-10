import AFTD.Prelude
import AFTD.Kb.Physics.HasDerivAtCompHasGradientAt
import AFTD.Kb.Physics.HasGradientAtInnerSelf

/-!
# hasGradientAt_norm

Topic: classical_mechanics   Node: 147d475fa9d3

Provenance: formalization of a published result. Source: Physlib, `hasGradientAt_norm`. Lean proof by Aadarsh Agarwal, Rithwik Ranganathan, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Gradient.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Away from the origin, the gradient of the norm is the unit vector `‖x‖⁻¹ • x`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open InnerProductSpace in
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {f g : F → ℝ} {f' g' : F} {x : F} in
/-- Away from the origin, the gradient of the norm is the unit vector `‖x‖⁻¹ • x`. -/
lemma hasGradientAt_norm (hx : x ≠ 0) : HasGradientAt (fun y : F => ‖y‖) (‖x‖⁻¹ • x) x := by
  have hs : ⟪x, x⟫_ℝ ≠ 0 := by simpa using hx
  have h := (Real.hasDerivAt_sqrt hs).comp_hasGradientAt (hasGradientAt_inner_self x)
  simp only [← norm_eq_sqrt_real_inner] at h
  convert h using 1
  rw [smul_smul]
  congr 1
  field_simp
