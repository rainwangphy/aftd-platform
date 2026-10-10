import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.ACCSystemGroupAction
import AFTD.Kb.Physics.ACCSystemSolsMulAction

/-!
# ACCSystemGroupAction.instGroupGroup

Topic: quantum_field_theory   Node: 82f3bb022ee8

Provenance: formalization of a published result. Source: Physlib, `ACCSystemGroupAction.instGroupGroup`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/AnomalyCancellation/GroupActions.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The given instance of a group on the `group` field of a `ACCSystemGroupAction`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The given instance of a group on the `group` field of a `ACCSystemGroupAction`. -/
instance ACCSystemGroupAction.instGroupGroup {χ : ACCSystem} (G : ACCSystemGroupAction χ) : Group G.group := G.groupInst
