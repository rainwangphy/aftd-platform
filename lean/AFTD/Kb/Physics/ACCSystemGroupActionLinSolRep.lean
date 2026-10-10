import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.ACCSystemGroupAction
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemGroupActionInstGroupGroup
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.ACCSystemGroupActionLinSolMap
import AFTD.Kb.Physics.ACCSystemLinearLinSolsExt
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemSolsMulAction

/-!
# ACCSystemGroupAction.linSolRep

Topic: quantum_field_theory   Node: 8af81b491f99

Provenance: formalization of a published result. Source: Physlib, `ACCSystemGroupAction.linSolRep`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/AnomalyCancellation/GroupActions.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The representation acting on the vector space of solutions to the linear ACCs.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The representation acting on the vector space of solutions to the linear ACCs. -/
@[simps!]
def ACCSystemGroupAction.linSolRep {χ : ACCSystem} (G : ACCSystemGroupAction χ) :
    Representation ℚ G.group χ.LinSols where
  toFun := G.linSolMap
  map_mul' g1 g2 := by
    refine LinearMap.ext fun S ↦ ACCSystemLinear.LinSols.ext ?_
    change (G.rep (g1 * g2)) S.val = _
    rw [G.rep.map_mul]
    rfl
  map_one' := by
    refine LinearMap.ext fun S ↦ ACCSystemLinear.LinSols.ext ?_
    change (G.rep.toFun 1) S.val = _
    rw [G.rep.map_one']
    rfl
