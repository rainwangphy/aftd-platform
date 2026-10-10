import AFTD.Prelude

/-!
# hasGradientAt_inner_left

Topic: classical_mechanics   Node: b2bd2eb71f27

Provenance: formalization of a published result. Source: Physlib, `hasGradientAt_inner_left`. Lean proof by Aadarsh Agarwal, Rithwik Ranganathan, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Gradient.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The gradient of `y ↦ ⟪a, y⟫` is `a`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open InnerProductSpace in
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {f g : F → ℝ} {f' g' : F} {x : F} in
/-- The gradient of `y ↦ ⟪a, y⟫` is `a`. -/
lemma hasGradientAt_inner_left (a x : F) : HasGradientAt (fun y : F => ⟪a, y⟫_ℝ) a x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  exact (toDual ℝ F a).hasFDerivAt
