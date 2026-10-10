import AFTD.Prelude

/-!
# gradient_coord

Topic: classical_mechanics   Node: c1045e65cb28

Provenance: formalization of a published result. Source: Physlib, `gradient_coord`. Lean proof by Aadarsh Agarwal, Rithwik Ranganathan, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Gradient.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The gradient of the `i`-th coordinate functional on Euclidean space is the `i`-th basis vector.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open InnerProductSpace in
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {f g : F → ℝ} {f' g' : F} {x : F} in
/-- The gradient of the `i`-th coordinate functional on Euclidean space is the `i`-th basis vector. -/
lemma gradient_coord {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) (x : EuclideanSpace ℝ ι) :
    gradient (fun y : EuclideanSpace ℝ ι => y i) x = EuclideanSpace.single i 1 := by
  have h : HasFDerivAt (fun y : EuclideanSpace ℝ ι => y i)
      (innerSL ℝ (EuclideanSpace.single i (1 : ℝ))) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.congr_fderiv
      (by ext y; simp [EuclideanSpace.inner_single_left])
  exact h.hasGradientAt.gradient.trans ((toDual ℝ _).symm_apply_apply _)
