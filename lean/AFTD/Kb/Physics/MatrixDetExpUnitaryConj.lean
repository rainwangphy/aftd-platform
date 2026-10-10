import AFTD.Prelude
import AFTD.Kb.Physics.MatrixExpUnitaryConj
import AFTD.Kb.Physics.MatrixDetUnitaryConj

/-!
# Matrix.det_exp_unitary_conj

Topic: classical_mechanics   Node: e7dbb1d3775b

Provenance: formalization of a published result. Source: Physlib, `Matrix.det_exp_unitary_conj`. Lean proof by Matteo Cipollina, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/DataStructures/Matrix/LieTrace.lean (Copyright (c) 2025 Matteo Cipollina. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.det_exp_unitary_conj
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
lemma Matrix.det_exp_unitary_conj (A : Matrix m m 𝕂) (U : unitaryGroup m 𝕂) :
    (NormedSpace.exp ((U : Matrix m m 𝕂) * A * star (U : Matrix m m 𝕂))).det =
    (NormedSpace.exp A).det := by
  rw [exp_unitary_conj, det_unitary_conj]
