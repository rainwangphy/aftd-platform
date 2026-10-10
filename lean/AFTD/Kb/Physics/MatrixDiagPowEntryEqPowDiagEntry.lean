import AFTD.Prelude
import AFTD.Kb.Physics.MatrixDiagPowOfBlockTriangularId
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# Matrix.diag_pow_entry_eq_pow_diag_entry

Topic: classical_mechanics   Node: bd45515ce8f1

Provenance: formalization of a published result. Source: Physlib, `Matrix.diag_pow_entry_eq_pow_diag_entry`. Lean proof by Matteo Cipollina, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/DataStructures/Matrix/LieTrace.lean (Copyright (c) 2025 Matteo Cipollina. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For an upper–triangular matrix `A`, the `(i,i)` entry of the power `A ^ n` is simply the `n`-th power of the original diagonal entry.
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
/-- For an upper–triangular matrix `A`, the `(i,i)` entry of the power `A ^ n` is simply the `n`-th power of the original diagonal entry. -/
lemma Matrix.diag_pow_entry_eq_pow_diag_entry {A : Matrix m m 𝕂}
    (hA : BlockTriangular A id) (n : ℕ) (i : m) :
    (A ^ n) i i = (A i i) ^ n := by
  have h := diag_pow_of_blockTriangular_id hA n
  simpa [diag_apply, Pi.pow_apply] using congr_arg (fun d => d i) h
