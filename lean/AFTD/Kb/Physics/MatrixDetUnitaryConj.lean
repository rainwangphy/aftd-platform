import AFTD.Prelude

/-!
# Matrix.det_unitary_conj

Topic: classical_mechanics   Node: 7c4aa74ae909

Provenance: formalization of a published result. Source: Physlib, `Matrix.det_unitary_conj`. Lean proof by Matteo Cipollina, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/DataStructures/Matrix/LieTrace.lean (Copyright (c) 2025 Matteo Cipollina. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The determinant is invariant under unitary conjugation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators Topology in
variable {𝕂 m n : Type*} in
variable [RCLike 𝕂] in
attribute [local instance] Matrix.linftyOpNormedAlgebra in
attribute [local instance] Matrix.linftyOpNormedRing in
attribute [local instance] Matrix.instCompleteSpace in
variable [Fintype m] [LinearOrder m] in
/-- The determinant is invariant under unitary conjugation. -/
lemma Matrix.det_unitary_conj (A : Matrix m m 𝕂) (U : unitaryGroup m 𝕂) :
    det ((U : Matrix m m 𝕂) * A * star (U : Matrix m m 𝕂)) = det A := by
  rw [det_mul_right_comm]
  simp_all only [SetLike.coe_mem, Unitary.mul_star_self_of_mem, one_mul]
