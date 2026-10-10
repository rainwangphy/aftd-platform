import AFTD.Prelude

/-!
# Matrix.trace_unitary_conj

Topic: classical_mechanics   Node: 5653785f12a4

Provenance: formalization of a published result. Source: Physlib, `Matrix.trace_unitary_conj`. Lean proof by Matteo Cipollina, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/DataStructures/Matrix/LieTrace.lean (Copyright (c) 2025 Matteo Cipollina. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The trace is invariant under unitary conjugation.
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
/-- The trace is invariant under unitary conjugation. -/
lemma Matrix.trace_unitary_conj (A : Matrix m m 𝕂) (U : unitaryGroup m 𝕂) :
    trace ((U : Matrix m m 𝕂) * A * star (U : Matrix m m 𝕂)) = trace A := by
  have h_unitary : star (U : Matrix m m 𝕂) * (U : Matrix m m 𝕂) = 1 :=
    UnitaryGroup.star_mul_self U
  simpa [Matrix.mul_assoc, h_unitary, Matrix.one_mul] using
    (Matrix.trace_mul_cycle (U : Matrix m m 𝕂) A (star (U : Matrix m m 𝕂)))
