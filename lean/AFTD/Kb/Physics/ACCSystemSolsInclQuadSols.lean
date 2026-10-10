import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.ACCSystemSolsMulAction
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction

/-!
# ACCSystem.solsInclQuadSols

Topic: quantum_field_theory   Node: 0edaf0bcf55c

Provenance: formalization of a published result. Source: Physlib, `ACCSystem.solsInclQuadSols`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The inclusion of `Sols` into `QuadSols`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The inclusion of `Sols` into `QuadSols`. -/
def ACCSystem.solsInclQuadSols (χ : ACCSystem) : χ.Sols →[ℚ] χ.QuadSols where
  toFun := Sols.toQuadSols
  map_smul' _ _ := rfl
