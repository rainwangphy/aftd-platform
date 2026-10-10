import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# Matrix.blockTriangular.pow

Topic: classical_mechanics   Node: 0bcafc2575a3

Provenance: formalization of a published result. Source: Physlib, `Matrix.blockTriangular.pow`. Lean proof by Matteo Cipollina, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/DataStructures/Matrix/LieTrace.lean (Copyright (c) 2025 Matteo Cipollina. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Powers of block triangular matrices are block triangular.
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
/-- Powers of block triangular matrices are block triangular. -/
lemma Matrix.blockTriangular.pow {A : Matrix m m 𝕂} (hA : BlockTriangular A id) (k : ℕ) :
    BlockTriangular (A ^ k) id := by
  induction k with
  | zero => rw [pow_zero]; exact blockTriangular_one
  | succ k ihk => rw [pow_succ]; exact ihk.mul hA
