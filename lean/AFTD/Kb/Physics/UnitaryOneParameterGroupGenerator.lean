import AFTD.Prelude
import AFTD.Kb.Physics.UnitaryOneParameterGroup
import AFTD.Kb.Physics.UnitaryOneParameterGroupInstCoeFunForallRealContinuousLinearMapComplexId
import AFTD.Kb.Physics.UnitaryOneParameterGroupAdjointEq

/-!
# UnitaryOneParameterGroup.generator

Topic: classical_mechanics   Node: ea107d987dcf

Provenance: formalization of a published result. Source: Physlib, `UnitaryOneParameterGroup.generator`. Lean proof by Tom Ole Diem, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/OneParameterSubgroups/Unitary.lean (Copyright (c) 2026 Tom Ole Diem. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The bounded self-adjoint generator of `U`, in the convention `U(t) = exp (-itA)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open UnitaryOneParameterGroup in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] in
/-- The bounded self-adjoint generator of `U`, in the convention `U(t) = exp (-itA)`. -/
noncomputable def UnitaryOneParameterGroup.generator (U : UnitaryOneParameterGroup H) : H →L[ℂ] H :=
  Complex.I • deriv U 0
