import AFTD.Prelude
import AFTD.Kb.Physics.HasDerivAtCompHasGradientAt
import AFTD.Kb.Physics.HasGradientAtCoord

/-!
# gradient_comp_coord

Topic: classical_mechanics   Node: ebc93232b40a

Provenance: formalization of a published result. Source: Physlib, `gradient_comp_coord`. Lean proof by Aadarsh Agarwal, Rithwik Ranganathan, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Gradient.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Chain rule for a function of one coordinate: the gradient of `y ↦ f (y i)` at `x` is `f' • EuclideanSpace.single i 1`, where `f'` is the derivative of `f` at `x i`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open InnerProductSpace in
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {f g : F → ℝ} {f' g' : F} {x : F} in
/-- Chain rule for a function of one coordinate: the gradient of `y ↦ f (y i)` at `x` is `f' • EuclideanSpace.single i 1`, where `f'` is the derivative of `f` at `x i`. -/
lemma gradient_comp_coord {ι : Type*} [Fintype ι] [DecidableEq ι] {f : ℝ → ℝ} {f' : ℝ}
    (i : ι) (x : EuclideanSpace ℝ ι) (hf : HasDerivAt f f' (x i)) :
    gradient (fun y : EuclideanSpace ℝ ι => f (y i)) x = f' • EuclideanSpace.single i 1 := by
  exact (hf.comp_hasGradientAt (hasGradientAt_coord i x)).gradient
