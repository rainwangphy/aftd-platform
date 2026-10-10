import AFTD.Prelude
import AFTD.Kb.Physics.MatrixBlockTriangularPow
import AFTD.Kb.Physics.MatrixDiagMulOfBlockTriangularId
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# Matrix.diag_pow_of_blockTriangular_id

Topic: classical_mechanics   Node: f5e01cdd525d

Provenance: formalization of a published result. Source: Physlib, `Matrix.diag_pow_of_blockTriangular_id`. Lean proof by Matteo Cipollina, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/DataStructures/Matrix/LieTrace.lean (Copyright (c) 2025 Matteo Cipollina. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For an upper-triangular matrix, the diagonal of a power is the power of the diagonal.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open scoped BigOperators Topology in
variable {𝕂 m n : Type*} in
variable [RCLike 𝕂] in
attribute [local instance] Matrix.linftyOpNormedAlgebra in
attribute [local instance] Matrix.linftyOpNormedRing in
attribute [local instance] Matrix.instCompleteSpace in
variable [Fintype m] [LinearOrder m] in
/-- For an upper-triangular matrix, the diagonal of a power is the power of the diagonal. -/
lemma Matrix.diag_pow_of_blockTriangular_id {A : Matrix m m 𝕂}
    (hA : BlockTriangular A id) (k : ℕ) : (A ^ k).diag = A.diag ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero]; simp [diag_one]
  | succ k ih =>
    have h_pow_k : BlockTriangular (A ^ k) id := blockTriangular.pow hA k
    rw [pow_succ, pow_succ, diag_mul_of_blockTriangular_id h_pow_k hA, ih]
