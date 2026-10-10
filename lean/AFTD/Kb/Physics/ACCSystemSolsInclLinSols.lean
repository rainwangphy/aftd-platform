import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.ACCSystemSolsMulAction
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsInclLinSols
import AFTD.Kb.Physics.ACCSystemSolsInclQuadSols

/-!
# ACCSystem.solsInclLinSols

Topic: quantum_field_theory   Node: c3ad2a0db365

Provenance: formalization of a published result. Source: Physlib, `ACCSystem.solsInclLinSols`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The inclusion of `Sols` into `LinSols`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The inclusion of `Sols` into `LinSols`. -/
def ACCSystem.solsInclLinSols (χ : ACCSystem) : χ.Sols →[ℚ] χ.LinSols :=
  MulActionHom.comp χ.quadSolsInclLinSols χ.solsInclQuadSols
