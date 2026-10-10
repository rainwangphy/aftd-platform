import AFTD.Prelude
import AFTD.Kb.Physics.GradientCoord

/-!
# hasGradientAt_coord

Topic: classical_mechanics   Node: 8864c3e50371

Provenance: formalization of a published result. Source: Physlib, `hasGradientAt_coord`. Lean proof by Aadarsh Agarwal, Rithwik Ranganathan, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Gradient.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The gradient of the `i`-th coordinate functional on Euclidean space is the `i`-th basis vector.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open InnerProductSpace in
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {f g : F → ℝ} {f' g' : F} {x : F} in
/-- The gradient of the `i`-th coordinate functional on Euclidean space is the `i`-th basis vector. -/
lemma hasGradientAt_coord {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι)
    (x : EuclideanSpace ℝ ι) :
    HasGradientAt (fun y : EuclideanSpace ℝ ι => y i) (EuclideanSpace.single i 1) x := by
  rw [← gradient_coord i x]
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.hasGradientAt
