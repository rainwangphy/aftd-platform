import AFTD.Prelude

/-!
# HasGradientAt.mul

Topic: classical_mechanics   Node: de8c94143868

Provenance: formalization of a published result. Source: Physlib, `HasGradientAt.mul`. Lean proof by Aadarsh Agarwal, Rithwik Ranganathan, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Gradient.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The gradient of a product is given by the Leibniz rule.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open InnerProductSpace in
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {f g : F → ℝ} {f' g' : F} {x : F} in
/-- The gradient of a product is given by the Leibniz rule. -/
lemma HasGradientAt.mul (hf : HasGradientAt f f' x) (hg : HasGradientAt g g' x) :
    HasGradientAt (fun y => f y * g y) (f x • g' + g x • f') x := by
  rw [hasGradientAt_iff_hasFDerivAt] at *
  simp only [map_add, map_smul]
  exact hf.mul hg
