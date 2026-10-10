import AFTD.Prelude
import AFTD.Kb.Physics.MatrixExpSeriesDiagTermEq
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# Matrix.matrix_exp_series_diag_eq_scalar_series

Topic: classical_mechanics   Node: f8d9d10a4ead

Provenance: formalization of a published result. Source: Physlib, `Matrix.matrix_exp_series_diag_eq_scalar_series`. Lean proof by Matteo Cipollina, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/DataStructures/Matrix/LieTrace.lean (Copyright (c) 2025 Matteo Cipollina. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The diagonal of the matrix exponential series equals the scalar exponential series
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
/-- The diagonal of the matrix exponential series equals the scalar exponential series -/
lemma Matrix.matrix_exp_series_diag_eq_scalar_series {A : Matrix m m 𝕂} (hA : BlockTriangular A id)
    (i : m) :
    (∑' n, ((n.factorial : 𝕂)⁻¹ • (A ^ n)) i i) = ∑' n, (n.factorial : 𝕂)⁻¹ • (A i i) ^ n := by
  exact tsum_congr (exp_series_diag_term_eq hA · i)
