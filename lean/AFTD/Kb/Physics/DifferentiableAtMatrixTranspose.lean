import AFTD.Prelude

/-!
# DifferentiableAt.matrix_transpose

Topic: classical_mechanics   Node: 480feaf79fc1

Provenance: formalization of a published result. Source: Physlib, `DifferentiableAt.matrix_transpose`. Lean proof by Giuseppe Sorge, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Time/MatrixDerivatives.lean (Copyright (c) 2026 Giuseppe Sorge. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The transpose of a differentiable matrix-valued function is differentiable (cf. `Continuous.matrix_transpose`).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold Matrix in
open scoped RightActions in
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
variable {d : ℕ} in
/-- The transpose of a differentiable matrix-valued function is differentiable (cf. `Continuous.matrix_transpose`). -/
lemma DifferentiableAt.matrix_transpose {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : E → Matrix (Fin d) (Fin d) ℝ} {t : E} (hA : DifferentiableAt ℝ A t) :
    DifferentiableAt ℝ (fun s => (A s)ᵀ) t :=
  ((transposeLinearEquiv (Fin d) (Fin d) ℝ ℝ).toLinearMap.toContinuousLinearMap).differentiableAt
    |>.comp t hA
