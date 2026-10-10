import AFTD.Prelude

/-!
# HasGradientAt.const_mul

Topic: classical_mechanics   Node: 3056aef74f30

Provenance: formalization of a published result. Source: Physlib, `HasGradientAt.const_mul`. Lean proof by Aadarsh Agarwal, Rithwik Ranganathan, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Gradient.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The gradient of a constant multiple is the constant multiple of the gradient.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open InnerProductSpace in
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {f g : F → ℝ} {f' g' : F} {x : F} in
/-- The gradient of a constant multiple is the constant multiple of the gradient. -/
lemma HasGradientAt.const_mul (c : ℝ) (hf : HasGradientAt f f' x) :
    HasGradientAt (fun y => c * f y) (c • f') x := by
  rw [hasGradientAt_iff_hasFDerivAt] at *
  simp only [map_smul]
  exact hf.const_mul c
