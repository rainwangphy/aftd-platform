import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.ACCSystemGroupAction
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsExt
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemSolsMulAction
import AFTD.Kb.Physics.ACCSystemGroupActionInstGroupGroup

/-!
# ACCSystemGroupAction.linSolMap

Topic: quantum_field_theory   Node: 257206868a2e

Provenance: formalization of a published result. Source: Physlib, `ACCSystemGroupAction.linSolMap`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/AnomalyCancellation/GroupActions.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The action of a group element on the vector space of linear solutions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The action of a group element on the vector space of linear solutions. -/
def ACCSystemGroupAction.linSolMap {χ : ACCSystem} (G : ACCSystemGroupAction χ) (g : G.group) :
    χ.LinSols →ₗ[ℚ] χ.LinSols where
  toFun S := ⟨G.rep g S.val, by
    intro i
    rw [G.linearInvariant, S.linearSol]⟩
  map_add' S T := ACCSystemLinear.LinSols.ext ((G.rep g).map_add' _ _)
  map_smul' a S := ACCSystemLinear.LinSols.ext ((G.rep g).map_smul' _ _)
