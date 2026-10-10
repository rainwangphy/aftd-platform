import AFTD.Prelude
import AFTD.Kb.Physics.UnitaryOneParameterGroup
import AFTD.Kb.Physics.UnitaryOneParameterGroupInstCoeFunForallRealContinuousLinearMapComplexId

/-!
# UnitaryOneParameterGroup.adjoint_eq

Topic: classical_mechanics   Node: 66fb0609ed35

Provenance: formalization of a published result. Source: Physlib, `UnitaryOneParameterGroup.adjoint_eq`. Lean proof by Tom Ole Diem, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/OneParameterSubgroups/Unitary.lean (Copyright (c) 2026 Tom Ole Diem. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

UnitaryOneParameterGroup.adjoint_eq
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open UnitaryOneParameterGroup in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] in
@[simp]
lemma UnitaryOneParameterGroup.adjoint_eq (U : UnitaryOneParameterGroup H) (t : ℝ) : (U t).adjoint = U (-t) := by
  apply left_inv_eq_right_inv (Unitary.star_mul_self_of_mem (U.mem_unitary t))
  simp [← AddChar.map_add_eq_mul]
