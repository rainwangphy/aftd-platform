import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.ACCSystemSolsMulAction
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsIncl
import AFTD.Kb.Physics.ACCSystemSolsInclQuadSols
import AFTD.Kb.Physics.ACCSystemSolsInclLinSols
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup

/-!
# ACCSystem.solsIncl

Topic: quantum_field_theory   Node: 1e5201a04c39

Provenance: formalization of a published result. Source: Physlib, `ACCSystem.solsIncl`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The inclusion of `Sols` into `LinSols`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The inclusion of `Sols` into `LinSols`. -/
def ACCSystem.solsIncl (χ : ACCSystem) : χ.Sols →[ℚ] χ.Charges :=
  MulActionHom.comp χ.quadSolsIncl χ.solsInclQuadSols
