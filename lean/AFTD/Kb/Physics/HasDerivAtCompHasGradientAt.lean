import AFTD.Prelude

/-!
# HasDerivAt.comp_hasGradientAt

Topic: classical_mechanics   Node: e043867fc9d4

Provenance: formalization of a published result. Source: Physlib, `HasDerivAt.comp_hasGradientAt`. Lean proof by Aadarsh Agarwal, Rithwik Ranganathan, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Gradient.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The gradient of `y ↦ φ (f y)` is `φ'` times the gradient of `f`, for `φ'` the derivative of `φ` at `f x`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open InnerProductSpace in
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {f g : F → ℝ} {f' g' : F} {x : F} in
/-- The gradient of `y ↦ φ (f y)` is `φ'` times the gradient of `f`, for `φ'` the derivative of `φ` at `f x`. -/
lemma HasDerivAt.comp_hasGradientAt {φ : ℝ → ℝ} {φ' : ℝ} (hf : HasGradientAt f f' x)
    (hφ : HasDerivAt φ φ' (f x)) : HasGradientAt (fun y => φ (f y)) (φ' • f') x := by
  rw [hasGradientAt_iff_hasFDerivAt] at *
  simp only [map_smul]
  exact hφ.comp_hasFDerivAt x hf
