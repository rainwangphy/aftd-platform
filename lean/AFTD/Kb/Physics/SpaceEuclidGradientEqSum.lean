import AFTD.Prelude

/-!
# Space.euclid_gradient_eq_sum

Topic: classical_mechanics   Node: bcbe8a7e41a7

Provenance: formalization of a published result. Source: Physlib, `Space.euclid_gradient_eq_sum`. Lean proof by Zhi Kai Pong, Joseph Tooby-Smith, Lode Vermeulen, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Derivatives/Grad.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Space.euclid_gradient_eq_sum
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open InnerProductSpace in
lemma Space.euclid_gradient_eq_sum {d} (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    gradient f x = ∑ i, fderiv ℝ f x (EuclideanSpace.single i 1) • EuclideanSpace.single i 1 := by
  apply ext_inner_right (𝕜 := ℝ) fun y => ?_
  simp [gradient]
  have hy : y = ∑ i, y i • EuclideanSpace.single i 1 := by
    conv_lhs => rw [← OrthonormalBasis.sum_repr (EuclideanSpace.basisFun (Fin d) ℝ) y]
    simp
  conv_lhs => rw [hy]
  simp [sum_inner, inner_smul_left, EuclideanSpace.inner_single_left, mul_comm]
