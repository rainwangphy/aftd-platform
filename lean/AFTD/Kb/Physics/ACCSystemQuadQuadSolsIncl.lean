import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemLinearLinSolsIncl
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsInclLinSols
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup

/-!
# ACCSystemQuad.quadSolsIncl

Topic: quantum_field_theory   Node: 4b6171c3f9ef

Provenance: formalization of a published result. Source: Physlib, `ACCSystemQuad.quadSolsIncl`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The inclusion of quadratic solutions into all charges.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The inclusion of quadratic solutions into all charges. -/
def ACCSystemQuad.quadSolsIncl (χ : ACCSystemQuad) : χ.QuadSols →[ℚ] χ.Charges :=
  MulActionHom.comp χ.linSolsIncl.toMulActionHom χ.quadSolsInclLinSols
