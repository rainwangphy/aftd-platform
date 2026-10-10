import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule

/-!
# ACCSystemQuad.quadSolsInclLinSols

Topic: quantum_field_theory   Node: 479165b4d2a2

Provenance: formalization of a published result. Source: Physlib, `ACCSystemQuad.quadSolsInclLinSols`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The inclusion of quadratic solutions into linear solutions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The inclusion of quadratic solutions into linear solutions. -/
def ACCSystemQuad.quadSolsInclLinSols (χ : ACCSystemQuad) : χ.QuadSols →[ℚ] χ.LinSols where
  toFun := QuadSols.toLinSols
  map_smul' _ _ := rfl
