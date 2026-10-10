import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction

/-!
# ACCSystem.IsSolution

Topic: quantum_field_theory   Node: af6a4512fe66

Provenance: formalization of a published result. Source: Physlib, `ACCSystem.IsSolution`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A charge `S` is a solution if it extends to a solution.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A charge `S` is a solution if it extends to a solution. -/
def ACCSystem.IsSolution (χ : ACCSystem) (S : χ.Charges) : Prop :=
  ∃ (sol : χ.Sols), sol.val = S
