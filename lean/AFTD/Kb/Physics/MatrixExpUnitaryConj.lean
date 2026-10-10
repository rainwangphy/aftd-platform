import AFTD.Prelude

/-!
# Matrix.exp_unitary_conj

Topic: classical_mechanics   Node: 1b723993e15d

Provenance: formalization of a published result. Source: Physlib, `Matrix.exp_unitary_conj`. Lean proof by Matteo Cipollina, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/DataStructures/Matrix/LieTrace.lean (Copyright (c) 2025 Matteo Cipollina. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The exponential of a matrix commutes with unitary conjugation.
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
/-- The exponential of a matrix commutes with unitary conjugation. -/
lemma Matrix.exp_unitary_conj (A : Matrix m m 𝕂) (U : unitaryGroup m 𝕂) :
    NormedSpace.exp ((U : Matrix m m 𝕂) * A * star (U : Matrix m m 𝕂)) =
      (U : Matrix m m 𝕂) * NormedSpace.exp A * star (U : Matrix m m 𝕂) := by
  let Uu : (Matrix m m 𝕂)ˣ :=
    { val := (U : Matrix m m 𝕂)
      inv := star (U : Matrix m m 𝕂)
      val_inv := by simp
      inv_val := by simp}
  have h_units := Matrix.exp_units_conj Uu A
  simpa [Uu] using h_units
