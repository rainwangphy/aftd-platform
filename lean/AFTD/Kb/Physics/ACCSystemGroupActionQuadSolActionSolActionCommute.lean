import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.ACCSystemGroupAction
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.ACCSystemSolsMulAction
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemSolsInclQuadSols
import AFTD.Kb.Physics.ACCSystemGroupActionInstGroupGroup
import AFTD.Kb.Physics.ACCSystemGroupActionSolAction
import AFTD.Kb.Physics.ACCSystemGroupActionQuadSolAction

/-!
# ACCSystemGroupAction.quadSolAction_solAction_commute

Topic: quantum_field_theory   Node: c2ff6952a677

Provenance: formalization of a published result. Source: Physlib, `ACCSystemGroupAction.quadSolAction_solAction_commute`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/AnomalyCancellation/GroupActions.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

ACCSystemGroupAction.quadSolAction_solAction_commute
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
lemma ACCSystemGroupAction.quadSolAction_solAction_commute {χ : ACCSystem} (G : ACCSystemGroupAction χ) (g : G.group)
    (S : χ.Sols) : χ.solsInclQuadSols (G.solAction.toFun _ _ S g) =
    G.quadSolAction.toFun _ _ (χ.solsInclQuadSols S) g := rfl
