import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# Matrix.diag_mul_of_blockTriangular_id

Topic: classical_mechanics   Node: 4ac4865de569

Provenance: formalization of a published result. Source: Physlib, `Matrix.diag_mul_of_blockTriangular_id`. Lean proof by Matteo Cipollina, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/DataStructures/Matrix/LieTrace.lean (Copyright (c) 2025 Matteo Cipollina. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For upper-triangular matrices, the diagonal of a product is the product of the diagonals. This is a specific case of a more general property for block-triangular matrices.
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
/-- For upper-triangular matrices, the diagonal of a product is the product of the diagonals. This is a specific case of a more general property for block-triangular matrices. -/
lemma Matrix.diag_mul_of_blockTriangular_id {A B : Matrix m m 𝕂}
    (hA : BlockTriangular A id) (hB : BlockTriangular B id) : (A * B).diag = A.diag * B.diag := by
  ext i
  simp only [diag_apply, mul_apply, Pi.mul_apply]
  apply Finset.sum_eq_single i
  · intro j _ j_ne_i
    cases lt_or_gt_of_ne j_ne_i with
    | inl h => rw [hA h, zero_mul] -- j < i
    | inr h => rw [hB h, mul_zero] -- i < j
  · intro; simp_all only [Finset.mem_univ, not_true_eq_false]
