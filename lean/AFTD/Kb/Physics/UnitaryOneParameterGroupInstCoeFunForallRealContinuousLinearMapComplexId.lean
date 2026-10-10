import AFTD.Prelude
import AFTD.Kb.Physics.UnitaryOneParameterGroup

/-!
# UnitaryOneParameterGroup.instCoeFunForallRealContinuousLinearMapComplexId

Topic: classical_mechanics   Node: b66a2c497c47

Provenance: formalization of a published result. Source: Physlib, `UnitaryOneParameterGroup.instCoeFunForallRealContinuousLinearMapComplexId`. Lean proof by Tom Ole Diem, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/OneParameterSubgroups/Unitary.lean (Copyright (c) 2026 Tom Ole Diem. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

UnitaryOneParameterGroup.instCoeFunForallRealContinuousLinearMapComplexId
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] in
noncomputable instance UnitaryOneParameterGroup.instCoeFunForallRealContinuousLinearMapComplexId : CoeFun (UnitaryOneParameterGroup H) fun _ => ℝ → (H →L[ℂ] H) := ⟨fun U => U.toAddChar⟩
