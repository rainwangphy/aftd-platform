import AFTD.Prelude
import AFTD.Kb.Physics.MatrixDiagPowEntryEqPowDiagEntry
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# Matrix.exp_series_diag_term_eq

Topic: classical_mechanics   Node: d9e735f17e3a

Provenance: formalization of a published result. Source: Physlib, `Matrix.exp_series_diag_term_eq`. Lean proof by Matteo Cipollina, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/DataStructures/Matrix/LieTrace.lean (Copyright (c) 2025 Matteo Cipollina. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Each term in the matrix exponential series equals the corresponding scalar term on the diagonal
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
/-- Each term in the matrix exponential series equals the corresponding scalar term on the diagonal -/
lemma Matrix.exp_series_diag_term_eq {A : Matrix m m 𝕂} (hA : BlockTriangular A id)
    (n : ℕ) (i : m) :
    ((n.factorial : 𝕂)⁻¹ • (A ^ n)) i i = (n.factorial : 𝕂)⁻¹ • (A i i) ^ n := by
  simp [smul_apply, diag_pow_entry_eq_pow_diag_entry hA]
